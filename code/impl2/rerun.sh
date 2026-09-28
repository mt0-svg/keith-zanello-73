#!/bin/sh
# Rerun checks of the second implementation and compare each output with the recorded one, ignoring running
# times, PARI's stack size warnings and trailing blanks.
# Usage: sh code/impl2/rerun.sh NAME ...   (NAME is the base name of a recorded output, e.g. engine_check)
# Needs sage and gp on the PATH. Exit status 0 when every output is identical to the recorded one.
# IMPL2_SAVE=dir (an absolute path) also writes the complete output of each rerun to dir/impl2/NAME.txt and a
# tab-separated result line (check, command, time, result, file) to dir/results/impl2_NAME.tsv.
set -u
cd "$(dirname "$0")"
cmd() {
  case $1 in
    engine_check|sturm_p73|search_p73_h3|spot_p73|lemma_sanity_p73|certificate_p73|sturm_p97|search_p97) echo "sage $1.sage" ;;
    brute_p73) echo "sage brute_p73.sage 16" ;;
    brute_p73_range_a) echo "sage brute_p73_range.sage 65536 163840 19" ;;
    brute_p73_range_b) echo "sage brute_p73_range.sage 163840 262144 19" ;;
    sparse_p73) echo "gp -q sparse_p73.gp" ;;
    sparse_p97) echo "gp -q -D parisizemax=2000000000 -D nbthreads=1 sparse_p97.gp" ;;
    sparse_direct_p73) echo "gp -q -D parisizemax=3000000000 -D nbthreads=1 sparse_direct_p73.gp" ;;
    leftovers_p73) echo "gp -q -D parisizemax=2500000000 -D nbthreads=1 leftovers_p73.gp" ;;
    sturm_p193) echo "sage sturm.sage 193 250" ;;
    sturm_p337) echo "sage sturm.sage 337 600" ;;
    sturm_p1033) echo "sage sturm.sage 1033 2100" ;;
    certificate_p193) echo "sage certificate.sage 193 tree" ;;
    certificate_p337) echo "sage certificate.sage 337" ;;
    certificate_p1033) echo "sage certificate.sage 1033" ;;
    *) return 1 ;;
  esac
}
norm() { grep -v -e '^\[[0-9.]* s\]$' -e '^[0-9.]* s [0-9]* KB$' -e 'Warning: .*stack size' "$1" | sed 's/[[:space:]]*$//'; }
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
status=0
for n in "$@"; do
  c=$(cmd "$n") || { echo "$n: unknown check"; status=1; continue; }
  start=$(date +%s)
  $c < /dev/null > "$TMP/$n.out" 2>&1
  secs=$(($(date +%s) - start))
  norm "$n.out" > "$TMP/old"
  norm "$TMP/$n.out" > "$TMP/new"
  if cmp -s "$TMP/old" "$TMP/new"; then
    r="PASS, identical to code/impl2/$n.out"
    echo "$n: identical to $n.out ($secs s)"
  else
    r="FAIL, different from code/impl2/$n.out"
    echo "$n: DIFFERENT from $n.out ($secs s)"
    diff "$TMP/old" "$TMP/new" | head -20
    status=1
  fi
  if [ -n "${IMPL2_SAVE:-}" ]; then
    mkdir -p "$IMPL2_SAVE/impl2" "$IMPL2_SAVE/results"
    cp "$TMP/$n.out" "$IMPL2_SAVE/impl2/$n.txt"
    printf "impl2 %s\t%s\t%s s\t%s\timpl2/%s.txt\n" "$n" "$c" "$secs" "$r" "$n" > "$IMPL2_SAVE/results/impl2_$n.tsv"
  fi
done
exit $status
