# bit3

LLVM IR → Lean 4 translator (`bitc`) and supporting Hoare-effect library (`bitlib`). See **[CONTEXT.md](./CONTEXT.md)** for domain vocabulary.

## Quick start

Install [just](https://just.systems) and [rustup](https://rustup.rs) (`cargo`), clone the repo, then:

```sh
just setup
just build
```

`just setup` installs LLVM, Lean (elan if needed), and Lake dependencies. The `bitc` Rust toolchain is pulled in automatically on the first `cargo` invocation during `just build`.

## Components

| Component | Path |
|-----------|------|
| Translator (Rust) | [`bitc/`](./bitc/) |
| Support library (Lean 4) | [`bitlib/`](./bitlib/) |
| Command runner & bootstrap scripts | [`justfile`](./justfile), [`just/`](./just/) |

Verification workflow: [VERIFICATION.md](./VERIFICATION.md).
