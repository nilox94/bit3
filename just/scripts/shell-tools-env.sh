#!/usr/bin/env bash
# Put managed shellcheck/shfmt installs on PATH for lint recipes.
#
# Resolution order:
#   1. Existing working binaries on PATH
#   2. Managed installs at ~/.local/shellcheck-* and ~/.local/shfmt-*

_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

shellcheck_version="$(tr -d '[:space:]' <"${_script_dir}/shellcheck-version")"
shfmt_version="$(tr -d '[:space:]' <"${_script_dir}/shfmt-version")"

shellcheck_prefix="${SHELLCHECK_PREFIX:-${HOME}/.local/shellcheck-${shellcheck_version}}"
shfmt_prefix="${SHFMT_PREFIX:-${HOME}/.local/shfmt-${shfmt_version}}"

_prepend_path() {
	case ":${PATH}:" in
	*":$1:"*) ;;
	*) export PATH="$1:${PATH}" ;;
	esac
}

configure_shell_tools_env() {
	if ! command -v shellcheck >/dev/null 2>&1; then
		if [[ -x "${shellcheck_prefix}/bin/shellcheck" ]]; then
			_prepend_path "${shellcheck_prefix}/bin"
		fi
	fi

	if ! command -v shfmt >/dev/null 2>&1; then
		if [[ -x "${shfmt_prefix}/bin/shfmt" ]]; then
			_prepend_path "${shfmt_prefix}/bin"
		fi
	fi

	if ! command -v shellcheck >/dev/null 2>&1; then
		echo "error: shellcheck not found" >&2
		echo "  Run: just setup" >&2
		return 1
	fi

	if ! command -v shfmt >/dev/null 2>&1; then
		echo "error: shfmt not found" >&2
		echo "  Run: just setup" >&2
		return 1
	fi
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
	configure_shell_tools_env || exit 1
else
	configure_shell_tools_env || return 1
fi
