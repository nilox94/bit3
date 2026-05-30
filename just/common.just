# Shared paths and toolchain pins.

root := justfile_directory()
scripts := root / "just/scripts"
llvm-version := trim(read(scripts / "llvm-version"))
llvm-prefix := home_directory() / ".local/llvm-" + llvm-version
shellcheck-version := trim(read(scripts / "shellcheck-version"))
shellcheck-prefix := home_directory() / ".local/shellcheck-" + shellcheck-version
shfmt-version := trim(read(scripts / "shfmt-version"))
shfmt-prefix := home_directory() / ".local/shfmt-" + shfmt-version
