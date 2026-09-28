#!/bin/sh
# Finiteness certificate tree at several primes; good lists from code/impl1/out/ker_eta_p<p>_b<B>.txt (t < 2^B, largest B).
# Usage: run_tree_multi.sh MU p1 p2 ...   (MU = bound on M in the sparse lemma; kstart = least k with 2^k >= p^2 + 40p)
# Output: code/impl1/out/tree_p<p>.txt
D=$(dirname "$0")
B=$(cd "$D/rust" && cargo build --release --quiet --bin kztree && cargo metadata --format-version 1 --no-deps | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')/release/kztree
MU=$1; shift
for p in "$@"; do
  K=$(ls $D/out/ker_eta_p${p}_b*.txt | sort | tail -1)
  G=$(grep -v "^#" $K | grep -v mode | tr '\n' ',' | sed 's/,$//')
  ks=$(gp -q -f <<GP
k = 1; while (2^k < $p^2 + 40*$p, k++); print(k)
GP
)
  echo "p=$p kstart=$ks mu=$MU list=$(basename $K) good=$G" > $D/out/tree_p${p}.txt
  /usr/bin/time -f "time %e s, maxrss %M KB" $B $p $ks $((ks + 8)) $((2 * p)) $MU $G >> $D/out/tree_p${p}.txt 2>&1
done
