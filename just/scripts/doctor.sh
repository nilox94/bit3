#!/usr/bin/env bash
# Verify toolchain — run via: just doctor

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

llvm_version="$(tr -d '[:space:]' <"${script_dir}/llvm-version")"
shellcheck_version="$(tr -d '[:space:]' <"${script_dir}/shellcheck-version")"
shfmt_version="$(tr -d '[:space:]' <"${script_dir}/shfmt-version")"

ok=0
check() {
	if "$@"; then
		printf '  ok  %s\n' "$*"
	else
		printf '  MISSING  %s\n' "$*"
		ok=1
	fi
}

echo "Pinned LLVM version (${script_dir}/llvm-version): ${llvm_version}"
echo "Pinned shellcheck (${script_dir}/shellcheck-version): ${shellcheck_version}"
echo "Pinned shfmt (${script_dir}/shfmt-version): ${shfmt_version}"

echo
echo "Prerequisites:"
check command -v just
check command -v cargo
check command -v lake

if command -v rustc >/dev/null 2>&1; then
	printf '  ok  rustc %s\n' "$(rustc --version | sed 's/^rustc //')"
else
	printf '  MISSING  rustc — install rustup: https://rustup.rs\n'
	ok=1
fi

echo
echo "Managed tools (just setup):"
# shellcheck source=shell-tools-env.sh disable=SC1091
if source "${script_dir}/shell-tools-env.sh" 2>/dev/null; then
	printf '  ok  shellcheck %s\n' "$(shellcheck --version | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)"
	printf '  ok  shfmt %s\n' "$(shfmt --version)"
else
	printf '  MISSING  shellcheck — run: just setup\n'
	printf '  MISSING  shfmt — run: just setup\n'
	ok=1
fi

echo
echo "LLVM (for bitc):"
# shellcheck source=llvm-env.sh disable=SC1091
if source "${script_dir}/llvm-env.sh" 2>/dev/null; then
	printf '  ok  llvm-config %s\n' "$(llvm-config --version)"
else
	printf '  MISSING  LLVM %s — run: just setup\n' "${llvm_version}"
	ok=1
fi

echo "Lean (install elan if missing — https://github.com/leanprover/elan):"
if command -v lake >/dev/null && command -v lean >/dev/null; then
	printf '  ok  %s\n' "$(lean --version | head -1)"
else
	printf '  MISSING  lake/lean — install elan, then run: just setup\n'
	ok=1
fi

exit "$ok"
