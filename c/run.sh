#!/bin/bash
# usage: run.sh logname "mode sign K1 K2" ...
cd "$(dirname "$0")"
log=../logs/$1; shift
for job in "$@"; do set -- $job; for K in $(seq $3 $4); do s=$(date +%s); ./lms4 $1 $2 $K | grep -E "SOL|DONE|WARN"; echo "mode=$1 sign=$2 K=$K t=$(( $(date +%s)-s ))s"; done; done >> $log 2>&1
