# bit3 — https://just.systems
#
# Prerequisites: rustup (cargo), elan (lake), just
# Bootstrap: just setup
#
# Recipes here; heavy logic in just/scripts/.

import 'just/common.just'

# Without `-c`, lines run in one script so `source` / `export` persist (see just manual).
set shell := ["bash", "-eu", "-o", "pipefail"]

sh_paths := scripts + "/*.sh"

[default]
[private]
list:
    @just --list --unsorted

# --- workspace (globals) ---

# Format all projects in-place.
fmt: bitc-fmt sh-fmt

# Read-only quality gates (fmt check + linters; no cargo check).
lint:
    just bitc-lint
    just sh-lint
    just bitlib-lint

# Build all project artifacts.
build: bitc-build bitlib-build

# Run all project tests.
test: bitc-test bitlib-test

# Remove build artifacts from all projects.
clean: bitc-clean bitlib-clean

# --- env ---

# Install managed toolchains (shell tools, LLVM, Lean/elan + lake deps).
[group('env')]
setup: setup-sh setup-llvm setup-lean
    @echo "Ready. Try: just build && just test"

# Install pinned shfmt and shellcheck under ~/.local.
[group('env')]
[private]
setup-sh:
    '{{ scripts }}/install-shellcheck.sh' --prefix '{{ shellcheck-prefix }}'
    '{{ scripts }}/install-shfmt.sh' --prefix '{{ shfmt-prefix }}'

# [*args] Install LLVM prebuilt (e.g. --prefix DIR, --github-env for CI).
[group('env')]
[private]
setup-llvm *args:
    '{{ scripts }}/setup-llvm.sh' {{ args }}

# Install Rust toolchain from bitc/rust-toolchain.toml.
[group('env')]
[private]
[working-directory('bitc')]
setup-rust:
    rustup toolchain install

# [--github-path] Install elan and refresh Lake package lock (CI: pass --github-path).
[group('env')]
[working-directory('bitlib')]
setup-lean *args:
    '{{ scripts }}/install-elan.sh' {{ args }}
    export PATH="${HOME}/.elan/bin:${PATH}"
    lake update

# Verify prerequisites and managed installs.
[group('env')]
doctor:
    '{{ scripts }}/doctor.sh'

# Remove managed toolchain installs from ~/.local.
[group('env')]
remove: remove-sh remove-llvm

[group('env')]
[private]
remove-sh:
    rm -rf '{{ shellcheck-prefix }}' '{{ shfmt-prefix }}'

[group('env')]
[private]
remove-llvm:
    rm -rf '{{ llvm-prefix }}'

# --- sh (just/scripts) ---

# [*paths] Format shell scripts in-place (default: all just/scripts/*.sh).
[group('sh')]
sh-fmt *paths=sh_paths:
    # shellcheck source=shell-tools-env.sh disable=SC1091
    source '{{ scripts }}/shell-tools-env.sh'
    shfmt -w {{ paths }}

# [*paths] Read-only: shfmt -d and shellcheck (default: all just/scripts/*.sh).
[group('sh')]
sh-lint *paths=sh_paths:
    # shellcheck source=shell-tools-env.sh disable=SC1091
    source '{{ scripts }}/shell-tools-env.sh'
    shfmt -d {{ paths }}
    shellcheck -x {{ paths }}

# --- bitc ---

# [*args] cargo fmt --all (e.g. --check for CI).
[group('bitc')]
bitc-fmt +args='': (bitc-cargo "fmt" "--all" args)

# [*args] cargo clippy.
[group('bitc')]
bitc-clippy +args='': (bitc-cargo "clippy" args)

# cargo fmt --check then clippy.
[group('bitc')]
bitc-lint: (bitc-cargo "fmt" "--all" "--check") bitc-clippy

# [*args] cargo build.
[group('bitc')]
bitc-build +args='': (bitc-cargo "build" args)

# [*args] cargo test.
[group('bitc')]
bitc-test +args='': (bitc-cargo "test" args)

# [*args] cargo run.
[group('bitc')]
bitc-run +args: (bitc-cargo "run" args)

# Print LLVM normalization pipeline phases.
[group('bitc')]
bitc-print-pipeline: (bitc-cargo "run" "--quiet" "--bin" "bitc-pipeline" "--" "phases")

# cargo clean.
[group('bitc')]
bitc-clean: (bitc-cargo "clean")

[private]
[working-directory('bitc')]
bitc-cargo +args:
    # shellcheck source=llvm-env.sh disable=SC1091
    source '{{ scripts }}/llvm-env.sh' && cargo {{ args }}

# --- bitlib ---

# [*args] lake build.
[group('bitlib')]
bitlib-build *args: (bitlib-lake "build" args)

# [*args] lake test.
[group('bitlib')]
bitlib-test *args: (bitlib-lake "test" args)

# [*args] lake lint.
[group('bitlib')]
bitlib-lint *args: (bitlib-lake "lint" args)

# lake clean.
[group('bitlib')]
bitlib-clean: (bitlib-lake "clean")

[private]
[working-directory('bitlib')]
bitlib-lake *args:
    lake {{ args }}
