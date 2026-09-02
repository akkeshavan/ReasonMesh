FROM rust:1.85-slim AS builder

WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY crates/ crates/

RUN cargo build --release -p reasonmesh-cli 2>&1 && \
    cargo test --release --workspace 2>&1

FROM debian:bookworm-slim AS runner

WORKDIR /app
COPY --from=builder /src/target/release/reasonmesh ./
COPY benchmarks/ benchmarks/
COPY experiments/ experiments/

# Port used by the NetBus TCP transport for peer-to-peer clause exchange.
EXPOSE 9000

ENTRYPOINT ["/app/reasonmesh"]
CMD ["--help"]
