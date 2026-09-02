//! rm-telemetry — metrics, traces, and deterministic replay logs.
//!
//! Every optimization in ReasonMesh must be measurable (spec §1). This crate
//! provides the machine-readable event vocabulary, the `.rmtrace` replay-log
//! format used by `reasonmesh replay`, and run-metrics aggregation over the
//! mandatory metric categories of spec §16.2.
//!
//! Determinism contract: sequence numbers are assigned monotonically per
//! worker timeline; the reader rejects traces whose sequence numbers are not
//! strictly increasing, and `TraceReader::replay_order` yields a canonical
//! deterministic ordering regardless of file interleaving.

pub mod event;
pub mod meta;
pub mod metrics;
pub mod trace;

pub use event::{DiscardReason, DropReason, Event, EventKind};
pub use meta::{now_nanos, HardwareMeta, Nanos, Outcome, RunMeta};
pub use metrics::RunMetrics;
pub use trace::{TraceError, TraceReader, TraceWriter};
