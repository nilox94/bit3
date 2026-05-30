#!/usr/bin/env bash
# Install shfmt prebuilt binary from GitHub releases.
#
# Usage:
#   ./scripts/install-shfmt.sh
#   ./scripts/install-shfmt.sh --prefix "$HOME/.local/shfmt-3.12.0"

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

log() { printf 'install-shfmt: %s\n' "$*" >&2; }
die() {
	log "error: $*"
	exit 1
}

default_version() {
	tr -d '[:space:]' <"${script_dir}/shfmt-version"
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
	x86_64 | amd64) echo amd64 ;;
	aarch64 | arm64) echo arm64 ;;
	*) die "unsupported architecture: $(uname -m)" ;;
	esac
}

asset_name() {
	local version="$1" os="$2" arch="$3"
	case "$os" in
	linux) echo "shfmt_v${version}_linux_${arch}" ;;
	darwin) echo "shfmt_v${version}_darwin_${arch}" ;;
	esac
}

download_url() {
	local version="$1" asset="$2"
	echo "https://github.com/mvdan/sh/releases/download/v${version}/${asset}"
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
			echo "Usage: install-shfmt.sh [--prefix DIR]"
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
	[[ -n "$version" ]] || die "no version (scripts/shfmt-version empty)"

	if [[ -z "$prefix" ]]; then
		prefix="${HOME}/.local/shfmt-${version}"
	fi

	local os arch asset url
	os="$(detect_os)"
	arch="$(detect_arch)"
	asset="$(asset_name "$version" "$os" "$arch")"
	url="$(download_url "$version" "$asset")"

	if [[ -x "${prefix}/bin/shfmt" ]]; then
		ver="$("${prefix}/bin/shfmt" --version)"
		ver="${ver#v}"
		if [[ "$ver" == "${version}" ]]; then
			log "already installed at ${prefix}"
			exit 0
		fi
	fi

	log "downloading ${asset}"
	rm -rf "$prefix"
	mkdir -p "${prefix}/bin"
	curl -fsSL -o "${prefix}/bin/shfmt" "$url"
	chmod +x "${prefix}/bin/shfmt"
	log "installed $("${prefix}/bin/shfmt" --version) at ${prefix}"
}

main "$@"
