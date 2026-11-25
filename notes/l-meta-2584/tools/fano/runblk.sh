#!/bin/bash
cd /tmp/claude-0/-home-user-pequalnp-proofs/760995d2-e961-5d2d-b429-03152e8426de/scratchpad/r/fano
q1(){ python3 -I topsat2.py 27 7 14 0-7,1-7,3-7,1-8,2-8,4-8,2-9,3-9,5-9,3-10,4-10,6-10,0-11,4-11,5-11,1-12,5-12,6-12,0-13,2-13,6-13 --timeout 1800; for t in 1 3 5 7 9 11 13; do python3 -I topsat2.py 26 $t 14 0-7,1-7,3-7,1-8,2-8,4-8,2-9,3-9,5-9,3-10,4-10,6-10,0-11,4-11,5-11,1-12,5-12,6-12,0-13,2-13,6-13 --timeout 1800; done; }
q2(){ for t in 2 4 6 8 10 12; do python3 -I topsat2.py 26 $t 14 0-7,1-7,3-7,1-8,2-8,4-8,2-9,3-9,5-9,3-10,4-10,6-10,0-11,4-11,5-11,1-12,5-12,6-12,0-13,2-13,6-13 --timeout 1800; done; }
q1 > blk_q1.log 2>&1 &
q2 > blk_q2.log 2>&1 &
wait; echo BLKDONE
