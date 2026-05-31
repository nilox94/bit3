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

# Print ok/MISSING for LABEL after running CMD (no silent failures in $()).
report_cmd() {
	local label="$1"
	shift
	local out=""
	if out="$("$@")"; then
		printf '  ok  %s %s\n' "$label" "$out"
	else
		printf '  MISSING  %s\n' "$label"
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
	_rustc_ver=""
	if _rustc_ver="$(rustc --version)"; then
		_rustc_ver="${_rustc_ver#rustc }"
		printf '  ok  rustc %s\n' "${_rustc_ver}"
	else
		printf '  MISSING  rustc\n'
		ok=1
	fi
else
	printf '  MISSING  rustc — install rustup: https://rustup.rs\n'
	ok=1
fi

echo
echo "Managed tools (just setup):"
# shellcheck source=shell-tools-env.sh disable=SC1091
if source "${script_dir}/shell-tools-env.sh"; then
	_sc_ver=""
	if _sc_ver="$(shellcheck --version | grep -oE '[0-9]+\.[0-9]+\.[0-9]+' | head -1)"; then
		printf '  ok  shellcheck %s\n' "${_sc_ver}"
	else
		printf '  MISSING  shellcheck\n'
		ok=1
	fi
	report_cmd shfmt shfmt --version
else
	printf '  MISSING  shellcheck — run: just setup\n'
	printf '  MISSING  shfmt — run: just setup\n'
	ok=1
fi

echo
echo "LLVM (for bitc):"
# shellcheck source=llvm-env.sh disable=SC1091
if source "${script_dir}/llvm-env.sh"; then
	report_cmd llvm-config llvm-config --version
else
	printf '  MISSING  LLVM %s — run: just setup\n' "${llvm_version}"
	ok=1
fi

echo "Lean (install elan if missing — https://github.com/leanprover/elan):"
if command -v lake >/dev/null 2>&1 && command -v lean >/dev/null 2>&1; then
	report_cmd lean lean --version
else
	printf '  MISSING  lake/lean — install elan, then run: just setup\n'
	ok=1
fi

exit "$ok"
