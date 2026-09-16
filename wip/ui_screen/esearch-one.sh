#!/bin/sh
# One bounded focused-search cell at S1: esearch-one.sh <delta> <side> <evalfuel> <sfuel> [bound]
BIN="$(dirname "$0")/../../.lake/build/bin/uifs"
T="${5:-900}"
line=$(perl -e "alarm $T; exec @ARGV" -- "$BIN" esearch "$1" "$2" "$3" "$4" 2>&1 | grep "^esearch" | head -1)
[ -z "$line" ] && line="esearch S1 delta=$1 side=$2 evalfuel=$3 sfuel=$4 UNSETTLED@${T}s"
echo "$line"
