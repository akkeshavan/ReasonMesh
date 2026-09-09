#!/usr/bin/env bash
# remote-setup.sh — installs all dependencies and builds ReasonMesh on a fresh Ubuntu 24.04 VM
#
# Called by provision.sh via:
#   ssh root@HOST bash -s -- <role> < scripts/remote-setup.sh
#
# Roles:
#   bench — CCX53: full setup (solver + Z3 + CaDiCaL + Kissat baselines)
#   node  — CCX23: solver only (for the distributed experiment)
#
# After this script completes:
#   /usr/local/bin/reasonmesh   — the solver binary
#   /usr/local/bin/z3           — Z3 (bench only)
#   /usr/local/bin/cadical      — CaDiCaL (bench only)
#   /usr/local/bin/kissat       — Kissat (bench only)
#   /opt/reasonmesh/            — cloned repo at v0.1.0.0

set -euo pipefail

ROLE="${1:-bench}"
REPO_TAG="v0.1.0.0"
REPO_URL="https://github.com/akkeshavan/ReasonMesh.git"
INSTALL_DIR="/opt/reasonmesh"
RUST_TOOLCHAIN="stable"

ts()  { date +%H:%M:%S; }
log() { echo "[setup:$ROLE $(ts)] $*"; }
step(){ echo -e "\n[setup:$ROLE $(ts)] ── $* ──"; }

# ── 1. System packages ────────────────────────────────────────────────────────
step "1/6  System packages"
log "apt-get update"
apt-get update -qq
log "apt-get update done"

PKGS=(
  build-essential   # gcc, make
  cmake             # needed by some crate build scripts
  git curl
  python3 python3-pip
  ca-certificates
  pkg-config
  libssl-dev
)

if [[ "$ROLE" == "bench" ]]; then
  # z3 from apt — Ubuntu 24.04 ships 4.12+, good enough for the baseline
  PKGS+=(z3)
  # perf tools — only needed on the bench node for profiling
  PKGS+=(linux-tools-common linux-tools-generic)
fi

log "apt-get install: ${PKGS[*]}"
apt-get install -y --no-install-recommends "${PKGS[@]}"
log "System packages installed"

# ── 2. Rust ───────────────────────────────────────────────────────────────────
step "2/6  Rust toolchain ($RUST_TOOLCHAIN)"
if ! command -v rustup &>/dev/null; then
  log "rustup not found — downloading installer"
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain "$RUST_TOOLCHAIN" --profile minimal --no-modify-path
  log "rustup install done"
else
  log "rustup already present"
fi
export PATH="$HOME/.cargo/bin:$PATH"
log "rustup update $RUST_TOOLCHAIN"
rustup update "$RUST_TOOLCHAIN"
log "  rustc $(rustc --version)"

# ── 3. Clone and build ReasonMesh ─────────────────────────────────────────────
step "3/6  Clone + cargo build reasonmesh-cli (5-10 min)"
log "Cloning ReasonMesh at tag $REPO_TAG into $INSTALL_DIR"
if [[ -d "$INSTALL_DIR" ]]; then
  log "  $INSTALL_DIR already exists — pulling latest"
  # Stash any rsynced source changes before checking out the tag
  git -C "$INSTALL_DIR" stash 2>/dev/null || true
  git -C "$INSTALL_DIR" fetch --tags
  git -C "$INSTALL_DIR" checkout "$REPO_TAG"
else
  git clone --branch "$REPO_TAG" --depth 1 "$REPO_URL" "$INSTALL_DIR"
fi

cd "$INSTALL_DIR"
log "cargo build --release -p reasonmesh-cli  [started at $(ts)]"
cargo build --release -p reasonmesh-cli 2>&1 | tail -5
ln -sf "$INSTALL_DIR/target/release/reasonmesh" /usr/local/bin/reasonmesh
log "cargo build done at $(ts): $(reasonmesh --version 2>/dev/null || echo 'built OK')"

# ── 4. Baseline solvers (bench role only) ────────────────────────────────────
if [[ "$ROLE" == "bench" ]]; then
  step "4/6  Baseline solvers (Z3 + CaDiCaL + Kissat)"

  # -- Z3 --
  log "z3 (apt): $(z3 --version)"

  # -- CaDiCaL --
  log "Building CaDiCaL  [started at $(ts)]"
  cd /tmp
  if [[ ! -d cadical ]]; then
    git clone --depth 1 https://github.com/arminbiere/cadical.git
  fi
  cd cadical
  if [[ ! -x build/cadical ]]; then
    ./configure
    make -j"$(nproc)"
  fi
  cp build/cadical /usr/local/bin/cadical
  log "CaDiCaL done at $(ts): $(cadical --version 2>&1 | head -1)"

  # -- Kissat --
  log "Building Kissat  [started at $(ts)]"
  cd /tmp
  if [[ ! -d kissat ]]; then
    git clone --depth 1 https://github.com/arminbiere/kissat.git
  fi
  cd kissat
  if [[ ! -x build/kissat ]]; then
    ./configure
    make -j"$(nproc)"
  fi
  cp build/kissat /usr/local/bin/kissat
  log "Kissat done at $(ts): $(kissat --version 2>&1 | head -1)"

else
  step "4/6  Baseline solvers — skipped (node role)"
fi

# ── 5. Python packages for analysis ───────────────────────────────────────────
step "5/6  Python analysis packages"
if [[ "$ROLE" == "bench" ]]; then
  log "pip3 install matplotlib pandas tabulate"
  pip3 install --break-system-packages --quiet matplotlib pandas tabulate
  log "Python packages installed"
else
  log "Skipped (node role)"
fi

# ── 6. System tuning ──────────────────────────────────────────────────────────
step "6/6  System tuning"

# Configure private network interface (enp7s0) if present but not yet UP.
# Hetzner attaches the private NIC but cloud-init sometimes misses it; bring
# it up via netplan so DHCP assigns the private IP and routes on every boot.
PRIV_IF="enp7s0"
PRIV_NETPLAN="/etc/netplan/60-private.yaml"
if ip link show "$PRIV_IF" &>/dev/null && [[ ! -f "$PRIV_NETPLAN" ]]; then
  log "Private NIC $PRIV_IF found without netplan config — writing and applying"
  cat > "$PRIV_NETPLAN" <<'NETPLAN'
network:
  version: 2
  ethernets:
    enp7s0:
      dhcp4: true
      dhcp4-overrides:
        use-dns: false
        use-routes: false
      routes:
        - to: 10.0.1.0/24
          via: 10.0.1.1
          metric: 100
NETPLAN
  chmod 600 "$PRIV_NETPLAN"
  ip link set "$PRIV_IF" up
  netplan apply
  sleep 3
  log "  enp7s0: $(ip addr show enp7s0 | grep 'inet ' || echo 'no inet addr yet')"
else
  log "Private NIC already configured — skipping"
fi

log "Setting CPU governor to performance"
for f in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
  echo performance > "$f" 2>/dev/null || true
done
log "CPU governor set"

log "Increasing open file limits (idempotent)"
grep -qF 'nofile 65535' /etc/security/limits.conf 2>/dev/null || cat >> /etc/security/limits.conf <<'EOF'
root soft nofile 65535
root hard nofile 65535
EOF
log "Limits updated"

# ── Done ──────────────────────────────────────────────────────────────────────
log "Setup complete at $(ts)"
log ""
log "Installed binaries:"
log "  reasonmesh : $(which reasonmesh)"
if [[ "$ROLE" == "bench" ]]; then
  log "  z3         : $(which z3)  ($(z3 --version))"
  log "  cadical    : $(which cadical)"
  log "  kissat     : $(which kissat)"
fi
