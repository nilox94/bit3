#!/usr/bin/env bash
# Resolve LLVM for bitc (llvm-sys / inkwell) and export env when needed.
#
# Resolution order:
#   1. Existing LLVM_SYS_<maj><min>_PREFIX if llvm-config works there
#   2. llvm-config on PATH if version matches LLVM_VERSION (no extra env)
#   3. Managed install at LLVM_PREFIX (default: ~/.local/llvm-<version>)
#
# Source from just/cargo wrappers — do not require callers to set LLVM_SYS_*.

_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${LLVM_VERSION:=$(tr -d '[:space:]' <"${_script_dir}/llvm-version")}"

_major="${LLVM_VERSION%%.*}"
_minor="${LLVM_VERSION#*.}"
_minor="${_minor%%.*}"
LLVM_SYS_VAR="LLVM_SYS_${_major}${_minor}_PREFIX"

managed_prefix="${LLVM_PREFIX:-${HOME}/.local/llvm-${LLVM_VERSION}}"

_version_ok() {
	local cfg="$1"
	"$cfg" --version 2>/dev/null | grep -Eq "^${_major}\\.${_minor}\\."
}

_apply_prefix() {
	local prefix="$1"
	export "${LLVM_SYS_VAR}=${prefix}"
	export PATH="${prefix}/bin:${PATH}"
	case "$(uname -s)" in
	Linux)
		export LD_LIBRARY_PATH="${prefix}/lib:${LD_LIBRARY_PATH:-}"
		;;
	Darwin)
		# Embed rpath at link time — DYLD_* is stripped/unreliable under task runners on macOS.
		export RUSTFLAGS="${RUSTFLAGS:-} -C link-arg=-Wl,-rpath,${prefix}/lib"
		;;
	esac
}

configure_llvm_env() {
	local _existing _prefix

	_existing="${!LLVM_SYS_VAR:-}"
	if [[ -n "$_existing" ]] && [[ -x "${_existing}/bin/llvm-config" ]] && _version_ok "${_existing}/bin/llvm-config"; then
		_apply_prefix "$_existing"
		return 0
	fi

	if command -v llvm-config >/dev/null 2>&1 && _version_ok llvm-config; then
		if [[ "$(uname -s)" == Darwin ]]; then
			_prefix="$(llvm-config --prefix)"
			export RUSTFLAGS="${RUSTFLAGS:-} -C link-arg=-Wl,-rpath,${_prefix}/lib"
		fi
		return 0
	fi

	if [[ -x "${managed_prefix}/bin/llvm-config" ]] && _version_ok "${managed_prefix}/bin/llvm-config"; then
		_apply_prefix "$managed_prefix"
		return 0
	fi

	echo "error: LLVM ${LLVM_VERSION} not found (need bin/llvm-config)." >&2
	echo "  Install: just setup" >&2
	echo "  Or set ${LLVM_SYS_VAR} to an existing prefix." >&2
	return 1
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
	configure_llvm_env || exit 1
else
	configure_llvm_env || return 1
fi
