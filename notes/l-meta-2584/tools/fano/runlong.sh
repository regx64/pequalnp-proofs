#!/bin/bash
# s = 26, at least 2 junk gates (L_meta_3760 + L_meta_1876 + L_meta_4183), Lemma V exact, 2 hours each, 3 at a time
cd /tmp/claude-0/-home-user-pequalnp-proofs/760995d2-e961-5d2d-b429-03152e8426de/scratchpad/r/fano
printf "%s\n" 11 10 9 | xargs -P 3 -I{} sh -c 'python3 -I topsat4.py 26 {} 14 0-7,1-7,3-7,1-8,2-8,4-8,2-9,3-9,5-9,3-10,4-10,6-10,0-11,4-11,5-11,1-12,5-12,6-12,0-13,2-13,6-13 --extra --lemmaV 7 --exactX --minand 2 --timeout 7200 > L26_t{}.log 2>&1'
echo LONGDONE
