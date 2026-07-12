#!/bin/sh
# laxrun — run the LaxLogic CLI (Main.lean → LaxLogic.PLLExec drivers).
#
# Interpreter path (`lake env lean --run`): works on the current toolchain,
# where the native `lake exe laxrun` binary crashes at startup due to a
# code-generator bug in the cache-shipped Mathlib C IR (NULL fields in
# `Set.instBoundedOrder`'s constant closure; full analysis in Main.lean).
# After a toolchain bump fixes that, this script can become:
#   exec lake exe laxrun "$@"
#
# Usage: scripts/laxrun.sh <subcommand> [args...]   (see `scripts/laxrun.sh help`)
cd "$(dirname "$0")/.." || exit 1
exec lake env lean --run Main.lean "$@"
