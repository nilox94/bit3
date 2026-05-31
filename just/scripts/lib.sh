#!/usr/bin/env bash
# Shared helpers for just/scripts (source only; not executed directly).

# Run "$@"; on failure call die with MSG. Use instead of "$(cmd)" inside log/printf.
run_or_die() {
	local _msg="$1"
	shift
	"$@" || die "$_msg"
}

# Assign stdout of "$@" to variable named by VAR; on failure call die with MSG.
capture_or_die() {
	local _var="$1" _msg="$2"
	shift 2
	local _out
	_out="$("$@")" || die "$_msg"
	printf -v "$_var" '%s' "$_out"
}
