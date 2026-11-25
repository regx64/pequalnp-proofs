#!/bin/bash
cd /tmp/claude-0/-home-user-pequalnp-proofs/760995d2-e961-5d2d-b429-03152e8426de/scratchpad/r
ex(){ R=$(python3 -I crit.py $2 $3); echo "== exhaustive n=$2 S=$1 E=$3"; DUMP=1 ./dumpc $1 $2 $3 $R | python3 -I rewrite.py $2 $3; }
sm(){ echo "== sampled n=$1 S=$3 E=$2 (400)"; python3 -I sampdump.py $1 $2 $3 400 | python3 -I rewrite.py $1 $2; }
( ex 8 6 0-1,0-2,0-3,1-4,2-5; ex 8 6 0-1,0-2,0-3,0-4,1-5 ) > it3_a.txt 2>&1 &
( ex 8 6 0-1,0-2,1-3,2-4,3-5; ex 7 5 0-1,0-2,1-3,2-4 ) > it3_b.txt 2>&1 &
( sm 8 0-1,0-2,0-3,0-4,4-5,4-6,4-7 11; sm 8 0-1,0-2,0-3,0-4,4-5,4-6,4-7 12; sm 7 0-4,0-5,0-6,1-4,2-5,3-6 11; sm 7 0-4,0-5,0-6,1-4,2-5,3-6 12 ) > it3_c.txt 2>&1 &
( sm 8 0-1,1-2,2-3,3-4,4-5,5-6,6-7,0-7 13; sm 8 0-1,1-2,2-3,3-4,4-5,5-6,6-7,0-7 14; sm 7 0-1,1-2,2-3,3-4,4-5,0-5,0-6 12; sm 7 0-1,1-2,2-3,3-4,4-5,5-6 11 ) > it3_d.txt 2>&1 &
wait; echo ITER3DONE
