#!/usr/bin/env bash
# Install shellcheck prebuilt binary from GitHub releases.
#
# Usage:
#   ./scripts/install-shellcheck.sh
#   ./scripts/install-shellcheck.sh --prefix "$HOME/.local/shellcheck-0.11.0"

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

log() { printf 'install-shellcheck: %s\n' "$*" >&2; }
die() {
	log "error: $*"
	exit 1
}

default_version() {
	tr -d '[:space:]' <"${script_dir}/shellcheck-version"
}

detect_os() {
	case "$(uname -s)" in
	Linux) echo linux ;;
	Darwin) echo darwin ;;
	*) die "unsupported OS: $(uname -s)" ;;
	esac
}

detect_arch() {
	case "$(uname -m)" in
	x86_64 | amd64) echo x86_64 ;;
	aarch64 | arm64) echo aarch64 ;;
	*) die "unsupported architecture: $(uname -m)" ;;
	esac
}

asset_name() {
	local version="$1" os="$2" arch="$3"
	echo "shellcheck-v${version}.${os}.${arch}.tar.xz"
}

download_url() {
	local version="$1" asset="$2"
	echo "https://github.com/koalaman/shellcheck/releases/download/v${version}/${asset}"
}

main() {
	local version="" prefix=""

	while [[ $# -gt 0 ]]; do
		case "$1" in
		--prefix)
			prefix="$2"
			shift 2
			;;
		-h | --help)
			echo "Usage: install-shellcheck.sh [--prefix DIR]"
			exit 0
			;;
		-*)
			die "unknown option: $1"
			;;
		*)
			[[ -z "$version" ]] || die "unexpected argument: $1"
			version="$1"
			shift
			;;
		esac
	done

	[[ -n "$version" ]] || version="$(default_version)"
	[[ -n "$version" ]] || die "no version (scripts/shellcheck-version empty)"

	if [[ -z "$prefix" ]]; then
		prefix="${HOME}/.local/shellcheck-${version}"
	fi

	local os arch asset url tmp binary
	os="$(detect_os)"
	arch="$(detect_arch)"
	asset="$(asset_name "$version" "$os" "$arch")"
	url="$(download_url "$version" "$asset")"

	if [[ -x "${prefix}/bin/shellcheck" ]] && "$prefix/bin/shellcheck" --version | grep -q "version: ${version}"; then
		log "already installed at ${prefix}"
		exit 0
	fi

	log "downloading ${asset}"
	tmp="$(mktemp -d "${TMPDIR:-/tmp}/install-shellcheck.XXXXXX")"
	curl -fsSL -o "${tmp}/${asset}" "$url"
	mkdir -p "${tmp}/extract"
	tar -xJf "${tmp}/${asset}" -C "${tmp}/extract"
	binary="$(find "${tmp}/extract" -name shellcheck -type f -perm +111 | head -1)"
	[[ -n "$binary" ]] || die "shellcheck binary not found in archive"

	rm -rf "$prefix"
	mkdir -p "${prefix}/bin"
	install -m 755 "$binary" "${prefix}/bin/shellcheck"
	rm -rf "$tmp"
	log "installed $("${prefix}/bin/shellcheck" --version | head -1) at ${prefix}"
}

main "$@"
