#!/usr/bin/env bash
# [--prefix DIR] [--github-env] [VERSION]
# Download and install official LLVM prebuilt binaries from llvm/llvm-project releases.
# Run via: just setup-llvm [prefix]
#
# Modern asset names (LLVM 19.1+):
#   LLVM-<version>-Linux-X64.tar.xz
#   LLVM-<version>-Linux-ARM64.tar.xz
#   LLVM-<version>-macOS-ARM64.tar.xz
#   LLVM-<version>-macOS-X64.tar.xz
#   LLVM-<version>-win64.exe
#   LLVM-<version>-woa64.exe
#
# Older releases use clang+llvm-<version>-<triple>.* — resolved by probing common triples
# (no version→URL asset list).
#
# Usage:
#   ./scripts/setup-llvm.sh 18.1.8
#   ./scripts/setup-llvm.sh 18.1.8 --prefix "$HOME/.local/llvm-18.1.8"
#   ./scripts/setup-llvm.sh 18.1.8 --prefix /tmp/llvm --github-env

set -euo pipefail

RELEASE_BASE="https://github.com/llvm/llvm-project/releases/download"

usage() {
	cat <<'EOF'
Usage: setup-llvm.sh [OPTIONS] [VERSION]

  VERSION   Full LLVM version (e.g. 18.1.8). Defaults to just/scripts/llvm-version.

Options:
  --prefix DIR       Install directory (default: $HOME/.local/llvm-VERSION)
  --github-env       Append LLVM_PATH, LLVM_SYS_<maj><min>_PREFIX, and LD_LIBRARY_PATH
                     to GITHUB_ENV (Linux) for GitHub Actions
  -h, --help         Show this help

After install, build bitc with:
  export LLVM_SYS_<maj><min>_PREFIX="<prefix>"
  export LD_LIBRARY_PATH="<prefix>/lib:${LD_LIBRARY_PATH:-}"   # Linux, if needed
EOF
}

log() { printf 'setup-llvm: %s\n' "$*" >&2; }
die() {
	log "error: $*"
	exit 1
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

default_llvm_version() {
	tr -d '[:space:]' <"${script_dir}/llvm-version"
}

# --- platform detection ---

detect_os() {
	case "$(uname -s)" in
	Darwin) echo darwin ;;
	Linux) echo linux ;;
	MINGW* | MSYS* | CYGWIN*) echo windows ;;
	*) die "unsupported OS: $(uname -s)" ;;
	esac
}

detect_arch() {
	local machine
	machine="$(uname -m)"
	case "$machine" in
	x86_64 | amd64) echo x64 ;;
	aarch64 | arm64) echo arm64 ;;
	*) die "unsupported architecture: $machine" ;;
	esac
}

# --- asset naming ---

# Modern single-file names (LLVM 19.1+).
modern_asset_name() {
	local version="$1" os="$2" arch="$3"
	case "$os" in
	linux)
		case "$arch" in
		x64) echo "LLVM-${version}-Linux-X64.tar.xz" ;;
		arm64) echo "LLVM-${version}-Linux-ARM64.tar.xz" ;;
		esac
		;;
	darwin)
		case "$arch" in
		x64) echo "LLVM-${version}-macOS-X64.tar.xz" ;;
		arm64) echo "LLVM-${version}-macOS-ARM64.tar.xz" ;;
		esac
		;;
	windows)
		case "$arch" in
		x64) echo "LLVM-${version}-win64.exe" ;;
		arm64) echo "LLVM-${version}-woa64.exe" ;;
		esac
		;;
	esac
}

# Legacy clang+llvm tarballs — try in order until one exists on the release.
legacy_asset_candidates() {
	local version="$1" os="$2" arch="$3"
	case "$os" in
	linux)
		if [[ "$arch" == arm64 ]]; then
			printf '%s\n' "clang+llvm-${version}-aarch64-linux-gnu.tar.xz"
		else
			local u
			for u in 22.04 20.04 18.04 16.04; do
				printf '%s\n' "clang+llvm-${version}-x86_64-linux-gnu-ubuntu-${u}.tar.xz"
			done
		fi
		;;
	darwin)
		if [[ "$arch" == arm64 ]]; then
			for suffix in \
				"arm64-apple-macos11" \
				"arm64-apple-darwin22.0" \
				"arm64-apple-darwin22.3.0" \
				"arm64-apple-darwin21.0"; do
				printf '%s\n' "clang+llvm-${version}-${suffix}.tar.xz"
			done
		else
			for suffix in \
				"x86_64-apple-darwin" \
				"x86_64-apple-darwin21.0"; do
				printf '%s\n' "clang+llvm-${version}-${suffix}.tar.xz"
			done
		fi
		;;
	windows)
		if [[ "$arch" == arm64 ]]; then
			echo "LLVM-${version}-woa64.exe"
		else
			echo "LLVM-${version}-win64.exe"
		fi
		;;
	esac
}

asset_exists() {
	local url="$1"
	local code
	code="$(curl -fsSL -o /dev/null -w '%{http_code}' -I "$url" 2>/dev/null || true)"
	[[ "$code" == "200" || "$code" == "302" ]]
}

resolve_asset() {
	local version="$1" os="$2" arch="$3"
	local tag="llvmorg-${version}"
	local modern name url

	modern="$(modern_asset_name "$version" "$os" "$arch")"
	url="${RELEASE_BASE}/${tag}/${modern}"
	if asset_exists "$url"; then
		echo "${modern}"
		return 0
	fi

	log "modern asset not found, probing legacy names…"
	while IFS= read -r name; do
		[[ -z "$name" ]] && continue
		url="${RELEASE_BASE}/${tag}/${name}"
		if asset_exists "$url"; then
			echo "${name}"
			return 0
		fi
	done < <(legacy_asset_candidates "$version" "$os" "$arch")

	die "no prebuilt binary found for ${version} on ${os}/${arch} (tag ${tag})"
}

download_url() {
	local version="$1" asset="$2"
	echo "${RELEASE_BASE}/llvmorg-${version}/${asset}"
}

# --- install ---

extract_archive() {
	local archive="$1" dest="$2"
	mkdir -p "$dest"
	case "$archive" in
	*.tar.xz)
		tar -xJf "$archive" -C "$dest"
		;;
	*.tar.gz)
		tar -xzf "$archive" -C "$dest"
		;;
	*)
		die "unsupported archive: $archive"
		;;
	esac
}

# Find directory containing bin/llvm-config under $1 (max depth 3).
find_llvm_prefix() {
	local root="$1"
	local found
	if [[ -x "${root}/bin/llvm-config" ]]; then
		echo "$root"
		return 0
	fi
	found="$(find "$root" -maxdepth 3 -path '*/bin/llvm-config' -print -quit 2>/dev/null || true)"
	if [[ -n "$found" ]]; then
		dirname "$(dirname "$found")"
		return 0
	fi
	die "llvm-config not found under ${root}"
}

llvm_sys_env_name() {
	local version="$1"
	local major minor
	major="${version%%.*}"
	minor="${version#*.}"
	minor="${minor%%.*}"
	echo "LLVM_SYS_${major}${minor}_PREFIX"
}

prefix_installed() {
	local prefix="$1" version="$2"
	[[ -x "${prefix}/bin/llvm-config" ]] &&
		"${prefix}/bin/llvm-config" --version 2>/dev/null | grep -q "^${version}"
}

# Fail if llvm-config cannot run (e.g. missing libtinfo.so.5 on Ubuntu before apt install).
verify_prefix() {
	local prefix="$1" version="$2"
	local installed_ver
	installed_ver="$("${prefix}/bin/llvm-config" --version)" ||
		die "llvm-config failed at ${prefix} (on Ubuntu try: apt install libtinfo5 zlib1g)"
	[[ "$installed_ver" == "${version}"* ]] ||
		die "llvm-config reports ${installed_ver}, expected ${version}"
}

emit_env() {
	local prefix="$1" version="$2" os="$3" github_env="$4"
	local llvm_sys_var
	llvm_sys_var="$(llvm_sys_env_name "$version")"

	if [[ "$github_env" -eq 1 ]]; then
		write_github_env "$prefix" "$llvm_sys_var" "$os"
	fi
}

write_github_env() {
	local prefix="$1" llvm_sys_var="$2" os="$3"
	: "${GITHUB_ENV:?GITHUB_ENV is not set}"
	{
		echo "LLVM_PATH=${prefix}"
		echo "${llvm_sys_var}=${prefix}"
		if [[ "$os" == linux ]]; then
			echo "LD_LIBRARY_PATH=${prefix}/lib:\${LD_LIBRARY_PATH:-}"
		fi
	} >>"$GITHUB_ENV"
}

# --- main ---

main() {
	local version="" prefix="" github_env=0

	while [[ $# -gt 0 ]]; do
		case "$1" in
		--prefix)
			prefix="$2"
			shift 2
			;;
		--github-env)
			github_env=1
			shift
			;;
		-h | --help)
			usage
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

	[[ -n "$version" ]] || version="$(default_llvm_version)"

	if [[ -z "$version" ]]; then
		usage
		exit 1
	fi

	if [[ ! "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
		die "VERSION must be full X.Y.Z (e.g. 18.1.8), got: ${version}"
	fi

	if [[ -z "$prefix" ]]; then
		prefix="${HOME}/.local/llvm-${version}"
	fi

	local os arch asset url
	os="$(detect_os)"
	arch="$(detect_arch)"

	if prefix_installed "$prefix" "$version"; then
		verify_prefix "$prefix" "$version"
		log "already installed at ${prefix}"
		emit_env "$prefix" "$version" "$os" "$github_env"
		exit 0
	fi

	if [[ "$os" == windows ]]; then
		die "Windows installer (.exe) is not supported by this script yet; use Linux or macOS tarballs"
	fi

	asset="$(resolve_asset "$version" "$os" "$arch")"
	url="$(download_url "$version" "$asset")"

	log "resolved ${asset}"
	log "installing to ${prefix}"

	local tmp archive staging tmp_parent
	tmp_parent="$(dirname "$prefix")"
	mkdir -p "$tmp_parent"
	tmp="$(mktemp -d "${tmp_parent}/.setup-llvm-${version}.XXXXXX")"
	archive="${tmp}/${asset}"
	staging="${tmp}/extract"

	curl -fsSL -o "$archive" "$url"
	extract_archive "$archive" "$staging"

	local extracted_prefix
	extracted_prefix="$(find_llvm_prefix "$staging")"

	rm -rf "$prefix"
	mkdir -p "$(dirname "$prefix")"
	mv "$extracted_prefix" "$prefix"
	rm -rf "$tmp"

	verify_prefix "$prefix" "$version"
	local installed_ver
	installed_ver="$("${prefix}/bin/llvm-config" --version)"
	log "installed ${installed_ver} at ${prefix}"
	emit_env "$prefix" "$version" "$os" "$github_env"
}

main "$@"
