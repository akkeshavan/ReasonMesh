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

ENTRYPOINT ["/app/reasonmesh"]
CMD ["--help"]
