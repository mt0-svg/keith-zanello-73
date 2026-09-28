#!/bin/sh
# Rebuild kztree, rerun the certificate at the given primes, and compare with the recorded outputs
# in ../code/impl1/out/tree_p<p>.txt. Running times and memory figures are ignored in the comparison.
# Usage: sh check.sh [p ...]        (default: 73 97 193; any prime of Table 2 is accepted)
# Needs: a Rust toolchain with cargo (the recorded runs used rustc 1.99 nightly); PARI/GP for the optional small checks (gp -q small_checks.gp).
# KZ_OUT=dir compares against dir/tree_p<p>.txt instead (used to test the checker on a tampered copy).
# KZ_SAVE=dir (an absolute path) also writes the complete output of each rerun, after the header line of the recorded
# file, to dir/impl1/tree_p<p>.txt, and a tab-separated result line (check, command, time, result, file) to
# dir/results/impl1_p<p>.tsv; LIST in the command is the list on the header line.
# Rerunning all 30 primes takes about 42 minutes on two threads (RAYON_NUM_THREADS=2).
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
CODE="$HERE/../code/impl1"
OUT="${KZ_OUT:-$CODE/out}"
cd "$CODE/rust"
cargo build --release --quiet --bin kztree
TARGET=$(cargo metadata --format-version 1 --no-deps | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')
BIN="$TARGET/release/kztree"
[ -x "$BIN" ] || { echo "kztree binary not found at $BIN"; exit 1; }
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
norm() { sed -e 's/\[[0-9.]* s\]//g' | grep -v '^time '; }
[ $# -gt 0 ] || set -- 73 97 193
status=0
for p in "$@"; do
  REC="$OUT/tree_p$p.txt"
  [ -f "$REC" ] || { echo "p=$p: no recorded output $REC"; status=1; continue; }
  HDR=$(head -1 "$REC")
  KS=$(echo "$HDR" | sed 's/.* kstart=\([0-9]*\) .*/\1/')
  MU=$(echo "$HDR" | sed 's/.* mu=\([0-9]*\) .*/\1/')
  GOOD=$(echo "$HDR" | sed 's/.* good=//')
  start=$(date +%s)
  "$BIN" "$p" "$KS" $((KS + 8)) $((2 * p)) "$MU" "$GOOD" > "$TMP/full.txt" 2>&1 || echo "kztree exited with status $?" >> "$TMP/full.txt"
  secs=$(($(date +%s) - start))
  # The recorded files hold the complete output (run_tree_multi.sh); only the timing lines are ignored.
  norm < "$TMP/full.txt" > "$TMP/new.txt"
  tail -n +2 "$REC" | norm > "$TMP/old.txt"
  if cmp -s "$TMP/new.txt" "$TMP/old.txt" && grep -q "^VERDICT: PASS" "$TMP/new.txt"; then
    echo "p=$p: identical to the recorded certificate, VERDICT PASS"
    r="PASS, identical to code/impl1/out/tree_p$p.txt"
  else
    echo "p=$p: DIFFERENT from the recorded certificate"
    diff "$TMP/old.txt" "$TMP/new.txt" | head -20
    r="FAIL, different from code/impl1/out/tree_p$p.txt"
    status=1
  fi
  if [ -n "${KZ_SAVE:-}" ]; then
    mkdir -p "$KZ_SAVE/impl1" "$KZ_SAVE/results"
    { echo "$HDR"; cat "$TMP/full.txt"; } > "$KZ_SAVE/impl1/tree_p$p.txt"
    printf 'kztree p=%s\tkztree %s %s %s %s %s LIST\t%s s\t%s\timpl1/tree_p%s.txt\n' \
      "$p" "$p" "$KS" $((KS + 8)) $((2 * p)) "$MU" "$secs" "$r" "$p" > "$KZ_SAVE/results/impl1_p$p.tsv"
  fi
done
exit $status
