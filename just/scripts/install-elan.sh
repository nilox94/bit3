#!/usr/bin/env bash
# [--github-path] Install elan (Lean version manager).
#
# Local: just setup-lean
# CI:    just setup-lean --github-path  (requires GITHUB_PATH; fails if unset)
# https://github.com/leanprover/elan

set -euo pipefail

ELAN_INIT_URL="https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
ELAN_BIN="${HOME}/.elan/bin"

log() { printf 'install-elan: %s\n' "$*" >&2; }
die() {
	log "error: $*"
	exit 1
}

_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${_script_dir}/lib.sh"

publish_elan_to_github_path() {
	[[ -n "${GITHUB_PATH:-}" ]] ||
		die "--github-path requires GITHUB_PATH (set by GitHub Actions)"
	echo "${ELAN_BIN}" >>"${GITHUB_PATH}"
}

verify_elan() {
	command -v lake >/dev/null 2>&1 || die "lake not on PATH after elan install"
	command -v lean >/dev/null 2>&1 || die "lean not on PATH after elan install"
	run_or_die "lean --version failed" lean --version >/dev/null
}

main() {
	local github_path=0

	while [[ $# -gt 0 ]]; do
		case "$1" in
		--github-path)
			github_path=1
			shift
			;;
		-h | --help)
			echo "Usage: install-elan.sh [--github-path]"
			exit 0
			;;
		*)
			die "unknown option: $1"
			;;
		esac
	done

	if command -v lake >/dev/null 2>&1 && command -v lean >/dev/null 2>&1; then
		verify_elan
		log "already installed"
		[[ "$github_path" -eq 1 ]] && publish_elan_to_github_path
		exit 0
	fi

	log "installing elan"
	curl -fsSL "${ELAN_INIT_URL}" | sh -s -- -y

	if ! command -v lake >/dev/null 2>&1; then
		export PATH="${ELAN_BIN}:${PATH}"
	fi

	verify_elan
	log "installed"
	[[ "$github_path" -eq 1 ]] && publish_elan_to_github_path
}

main "$@"
