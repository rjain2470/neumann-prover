
set -euo pipefail

if ! command -v elan >/dev/null 2>&1; then
  echo "[neumann] Installing elan..."
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi

source "$HOME/.elan/env"

# Pin Lean toolchain
LEAN_TOOLCHAIN="leanprover/lean4:v4.22.0"
elan toolchain install "$LEAN_TOOLCHAIN" || true
elan default "$LEAN_TOOLCHAIN"

# Create (or reuse) a Lean project directory
LEAN_DIR="$HOME/lean_project"
mkdir -p "$LEAN_DIR"
cd "$LEAN_DIR"

echo "$LEAN_TOOLCHAIN" > lean-toolchain

# 5) Minimal Lakefile pinned to Mathlib v4.22.0
cat > lakefile.lean <<'EOF'
import Lake
open Lake DSL

package lean_project

require «mathlib» from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"
EOF

echo "[neumann] Running lake update..."
lake update

echo "[neumann] Fetching Mathlib cache..."
lake exe cache get || true

echo "✅ Lean + Mathlib set up at $LEAN_DIR"
