//! `.rmtrace` replay logs.
//!
//! Format: newline-delimited JSON. The first line is the `RunMeta` header;
//! every following line is one `Event`. The reader validates that sequence
//! numbers are strictly increasing within each worker's timeline, which
//! guarantees the logical event ordering required for deterministic replay
//! (spec §15.3). Exact timestamps are informational only.

use crate::event::{Event, EventKind};
use crate::meta::{now_nanos, RunMeta};
use crate::metrics::RunMetrics;
use rm_akx::reasoner::WorkerId;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::io::{self, BufRead, Write};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TraceError {
    #[error("io error: {0}")]
    Io(#[from] io::Error),
    #[error("malformed trace: {0}")]
    Json(#[from] serde_json::Error),
    #[error("unsupported trace schema version {0} (this build supports {1})")]
    SchemaVersion(u32, u32),
    #[error("trace is empty: missing header")]
    Empty,
    #[error(
        "sequence numbers are not strictly increasing on worker {worker} (got {seq} after {prev})"
    )]
    OutOfOrder { worker: u32, seq: u64, prev: u64 },
    #[error("sequence number {seq} on worker {worker} is not greater than the previous {prev}")]
    NonIncreasing { worker: u32, seq: u64, prev: u64 },
}

/// Append events to a trace file, assigning timeline-local sequence numbers.
pub struct TraceWriter<W: Write> {
    out: W,
    meta: RunMeta,
    seq: BTreeMap<u32, u64>,
}

impl<W: Write> TraceWriter<W> {
    /// Begin a new trace: write the header, then accept events.
    pub fn new(out: W, meta: RunMeta) -> Result<Self, TraceError> {
        let mut w = TraceWriter {
            out,
            meta,
            seq: BTreeMap::new(),
        };
        let header = Header {
            kind: HeaderKind::RunMeta,
            meta: w.meta.clone(),
        };
        serde_json::to_writer(&mut w.out, &header)?;
        w.out.write_all(b"\n")?;
        Ok(w)
    }

    /// Record an event with the current wall-clock timestamp. Returns the
    /// assigned sequence number.
    pub fn record(&mut self, worker: WorkerId, kind: EventKind) -> Result<u64, TraceError> {
        self.record_at(worker, now_nanos(), kind)
    }

    /// Record an event with an explicit timestamp (e.g. a replayed one).
    pub fn record_at(
        &mut self,
        worker: WorkerId,
        at_nanos: u128,
        kind: EventKind,
    ) -> Result<u64, TraceError> {
        let seq = self.seq.entry(worker.0).or_insert(0);
        *seq += 1;
        let event = Event {
            seq: *seq,
            worker: worker.0,
            at_nanos,
            kind,
        };
        serde_json::to_writer(&mut self.out, &event)?;
        self.out.write_all(b"\n")?;
        Ok(event.seq)
    }

    pub fn into_inner(self) -> W {
        self.out
    }

    pub fn meta(&self) -> &RunMeta {
        &self.meta
    }
}

/// Read and validate a trace file.
#[derive(Debug)]
pub struct TraceReader {
    meta: RunMeta,
    events: Vec<Event>,
}

impl TraceReader {
    /// Read the header and all events, validating per-timeline ordering.
    pub fn open<R: BufRead>(mut rd: R) -> Result<Self, TraceError> {
        let mut header_line = String::new();
        rd.read_line(&mut header_line)?;
        if header_line.trim().is_empty() {
            return Err(TraceError::Empty);
        }
        let header: Header = serde_json::from_str(&header_line)?;
        if header.kind != HeaderKind::RunMeta {
            return Err(TraceError::Json(serde_json::Error::io(io::Error::new(
                io::ErrorKind::InvalidData,
                "first line is not a RunMeta header",
            ))));
        }
        let meta = header.meta;
        if meta.schema_version != crate::meta::TRACE_SCHEMA_VERSION {
            return Err(TraceError::SchemaVersion(
                meta.schema_version,
                crate::meta::TRACE_SCHEMA_VERSION,
            ));
        }

        let mut events = Vec::new();
        let mut last_seq: BTreeMap<u32, u64> = BTreeMap::new();
        for line in rd.lines() {
            let line = line?;
            let line = line.trim();
            if line.is_empty() {
                continue;
            }
            let event: Event = serde_json::from_str(line)?;
            match last_seq.get(&event.worker) {
                None => {
                    last_seq.insert(event.worker, event.seq);
                }
                Some(&prev) => {
                    if event.seq <= prev {
                        return Err(TraceError::NonIncreasing {
                            worker: event.worker,
                            seq: event.seq,
                            prev,
                        });
                    }
                    last_seq.insert(event.worker, event.seq);
                }
            }
            events.push(event);
        }

        Ok(TraceReader { meta, events })
    }

    pub fn meta(&self) -> &RunMeta {
        &self.meta
    }

    pub fn events(&self) -> &[Event] {
        &self.events
    }

    /// Deterministic replay order: events grouped by worker, each worker's
    /// timeline in sequence order, workers sorted by id. This is the canonical
    /// ordering regardless of interleaving in the file.
    pub fn replay_order(&self) -> Vec<&Event> {
        let mut by_worker: BTreeMap<u32, Vec<&Event>> = BTreeMap::new();
        for e in &self.events {
            by_worker.entry(e.worker).or_default().push(e);
        }
        let mut out = Vec::with_capacity(self.events.len());
        for evs in by_worker.values_mut() {
            evs.sort_by_key(|e| e.seq);
            out.extend(evs.iter().copied());
        }
        out
    }

    /// Fold all events into run metrics (spec §16.2).
    pub fn summarize(&self) -> RunMetrics {
        RunMetrics::summarize(&self.events)
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct Header {
    kind: HeaderKind,
    meta: RunMeta,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
enum HeaderKind {
    RunMeta,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::event::{DiscardReason, EventKind};
    use crate::meta::{HardwareMeta, Nanos, Outcome, RunMeta};
    use rm_akx::knowledge::{KnowledgeId, KnowledgeKindTag};

    fn sample_meta() -> RunMeta {
        RunMeta {
            schema_version: 1,
            solver_version: "0.1.0-test".into(),
            git_revision: "abc123".into(),
            command_line: "reasonmesh solve test.cnf".into(),
            num_workers: 2,
            seeds: vec![1, 2],
            deterministic: false,
            hardware: HardwareMeta {
                os: "test".into(),
                arch: "test".into(),
                cpu_count: 2,
            },
            started_at: 0,
        }
    }

    fn round_trip(writer: impl FnOnce(&mut TraceWriter<&mut Vec<u8>>)) -> TraceReader {
        let mut buf = Vec::new();
        {
            let mut w = TraceWriter::new(&mut buf, sample_meta()).unwrap();
            writer(&mut w);
        }
        TraceReader::open(&buf[..]).unwrap()
    }

    #[test]
    fn round_trips_header_and_events() {
        let r = round_trip(|w| {
            w.record(
                WorkerId(0),
                EventKind::Phase {
                    name: "root".into(),
                },
            )
            .unwrap();
            w.record(
                WorkerId(0),
                EventKind::KnowledgeGenerated {
                    id: KnowledgeId(1),
                    kind: KnowledgeKindTag::Clause,
                    size: 3,
                    lbd: 2,
                },
            )
            .unwrap();
            w.record(WorkerId(1), EventKind::Restart { assumed: 1 })
                .unwrap();
            w.record(
                WorkerId(0),
                EventKind::RunFinished {
                    outcome: Outcome::Sat,
                },
            )
            .unwrap();
        });
        assert_eq!(r.meta().num_workers, 2);
        assert_eq!(r.events().len(), 4);
        // Per-timeline sequence numbers.
        assert_eq!(r.events()[0].seq, 1);
        assert_eq!(r.events()[1].seq, 2);
        assert_eq!(r.events()[2].seq, 1);
        assert_eq!(r.events()[3].seq, 3);
    }

    #[test]
    fn replay_order_groups_by_worker_then_seq() {
        let r = round_trip(|w| {
            // Interleaved on purpose.
            w.record(WorkerId(1), EventKind::Restart { assumed: 0 })
                .unwrap();
            w.record(WorkerId(0), EventKind::Phase { name: "a".into() })
                .unwrap();
            w.record(WorkerId(1), EventKind::Restart { assumed: 0 })
                .unwrap();
            w.record(WorkerId(0), EventKind::Phase { name: "b".into() })
                .unwrap();
        });
        let order = r.replay_order();
        let workers: Vec<u32> = order.iter().map(|e| e.worker).collect();
        // All worker-0 events before all worker-1 events.
        assert_eq!(workers, vec![0, 0, 1, 1]);
        assert!(order[0].seq < order[1].seq);
        assert!(order[2].seq < order[3].seq);
    }

    #[test]
    fn rejects_out_of_order_sequence() {
        let mut buf = Vec::new();
        {
            let mut w = TraceWriter::new(&mut buf, sample_meta()).unwrap();
            w.record(WorkerId(0), EventKind::Phase { name: "a".into() })
                .unwrap();
            w.record(WorkerId(0), EventKind::Phase { name: "b".into() })
                .unwrap();
        }
        // Corrupt: duplicate the first event line so seq goes 1,1,2.
        let text = String::from_utf8(buf).unwrap();
        let mut lines: Vec<&str> = text.lines().collect();
        let first_event = lines[1].to_string();
        lines.insert(2, &first_event);
        let corrupted = lines.join("\n");
        let err = TraceReader::open(corrupted.as_bytes()).unwrap_err();
        assert!(matches!(
            err,
            TraceError::NonIncreasing {
                worker: 0,
                seq: 1,
                prev: 1
            }
        ));
    }

    #[test]
    fn rejects_unknown_schema_version() {
        let mut meta = sample_meta();
        meta.schema_version = 99;
        let mut buf = Vec::new();
        {
            let mut w = TraceWriter::new(&mut buf, meta).unwrap();
            w.record(WorkerId(0), EventKind::Phase { name: "a".into() })
                .unwrap();
        }
        let err = TraceReader::open(&buf[..]).unwrap_err();
        assert!(matches!(err, TraceError::SchemaVersion(99, 1)));
    }

    #[test]
    fn rejects_empty_trace() {
        let err = TraceReader::open(&b""[..]).unwrap_err();
        assert!(matches!(err, TraceError::Empty));
    }

    #[test]
    fn metrics_aggregate_events() {
        let r = round_trip(|w| {
            for _ in 0..3 {
                w.record(
                    WorkerId(0),
                    EventKind::Conflict {
                        level: 1,
                        learnt_len: 2,
                        learnt_lbd: 1,
                    },
                )
                .unwrap();
            }
            w.record(WorkerId(0), EventKind::Propagation { count: 42 })
                .unwrap();
            w.record(
                WorkerId(0),
                EventKind::KnowledgeGenerated {
                    id: KnowledgeId(1),
                    kind: KnowledgeKindTag::Clause,
                    size: 3,
                    lbd: 2,
                },
            )
            .unwrap();
            w.record(
                WorkerId(0),
                EventKind::BatchPublished {
                    from: 0,
                    to: 1,
                    count: 2,
                    bytes: 64,
                },
            )
            .unwrap();
            w.record(
                WorkerId(0),
                EventKind::KnowledgeDiscarded {
                    id: KnowledgeId(2),
                    kind: KnowledgeKindTag::Clause,
                    reason: DiscardReason::Duplicate,
                },
            )
            .unwrap();
            w.record(
                WorkerId(0),
                EventKind::RunFinished {
                    outcome: Outcome::Unsat,
                },
            )
            .unwrap();
        });
        let m = r.summarize();
        assert_eq!(m.outcome, Some(Outcome::Unsat));
        assert_eq!(m.conflicts, 3);
        assert_eq!(m.propagations, 42);
        assert_eq!(m.generated, 1);
        assert_eq!(m.discarded, 1);
        assert_eq!(m.bytes_sent, 64);
        assert!(m.wall_nanos.is_some());
    }

    #[test]
    fn writer_assigns_monotonic_seq_per_worker() {
        let mut buf = Vec::new();
        let mut w = TraceWriter::new(&mut buf, sample_meta()).unwrap();
        let a1 = w
            .record(WorkerId(0), EventKind::Phase { name: "x".into() })
            .unwrap();
        let b1 = w
            .record(WorkerId(3), EventKind::Phase { name: "y".into() })
            .unwrap();
        let a2 = w
            .record(WorkerId(0), EventKind::Phase { name: "z".into() })
            .unwrap();
        assert_eq!((a1, b1, a2), (1, 1, 2));
        assert!(a2 > a1);
    }

    #[allow(dead_code)]
    fn _nanos(_: Nanos) {}
}
