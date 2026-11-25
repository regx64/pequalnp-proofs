# L-meta-2584: research notes, iteration 1

Statement (L-meta-2584): for a 4-cycle-free incidence structure, every `IsAO2` circuit for the
incidence function has a no-larger `IsAO2` circuit for it that is read-2 (`ReadK.IsReadK _ _ 2`).

Nothing here is submitted. Nothing here is checked by the project's checker. The Lean file builds
locally against upstream `main` (fcd57be2) with the pinned toolchain; its axioms are `propext`,
`Classical.choice`, `Quot.sound`. Everything else is computed data, not proof.

## Equivalences

* E1 (`Equiv2584.lean`, builds locally): for a fixed incidence structure, the statement holds iff
  some least `IsAO2` circuit for the function is read-2.
* E2: the lower bound "least size = E + tau - 1" implies the statement (the star cover of
  `L_meta_7684` is read-1).
* E3: "some least circuit is read-1" is equivalent to that lower bound, by the checked
  `L_meta_6369` (read-1 gives E + tau <= size + 1) and `L_meta_7684`. A read-1 target is
  therefore circular; read-2 is the only target here that avoids the lower bound.

## Computed data (tools/)

* `census-n6.txt`: every bipartite graph on at most 6 vertices without isolated vertices (34 up
  to isomorphism). All least `IsAO2`-type circuits enumerated (AND/OR on two distinct earlier
  wires, no copy gate, distinct wire functions, every gate read), each classified by its exact
  read number.
  * 4-cycle-free (20 graphs): least size = E + tau - 1 in every case; a read-1 least circuit
    exists in every case.
  * with a 4-cycle (14 graphs): least size < E + tau - 1 in every case; a read-1 least circuit
    still exists in every case.
  * Not every least circuit is read-2: the tree 0-1,0-2,0-3,1-4,2-5 has 43 least circuits (7
    gates), 2 of them read-3 (edge {1,4} reads x1 three times).
* `normalization-n6.txt`: the implicant lift (wire below F read by an OR outside the top OR-tree
  moved to the output; size kept) applied to a fixed point, then the read number again.
  * At least size and least size + 1 on the 4-cycle-free graphs tried: every normalized circuit
    is read <= 2.
  * At least size + 2: normalized read-3 circuits exist even on the path P4 (0-1,0-2,1-3), e.g.
    OR(0,1) OR(1,2) OR(0,3) AND(4,5) AND(4,6) AND(7,8): edge {1,3} reads x1 three times.
  * The lift fixed point of the checked `L_meta_3762` (a 4-cycle-free tree, 11 gates, least 8)
    is read-4 (edge (0,4)), computed with `tools/readk.py`.
  * Every normalized read->=3 circuit found on the 4-cycle-free graphs (166) has a gate that can
    be deleted with its reads redirected to an existing wire; the `L_meta_3762` circuit has none
    (it needs (s|A)&(s|B) -> s|(A&B), 3 gates to 2, after which it is read-2 with 10 gates).

## Directions ruled out by the data

* "every least circuit is read-2": false (tree above).
* "every lift fixed point is read-2": false (P4 example, `L_meta_3762`).
* "a non-read-2 lift fixed point has a deletable gate": false (`L_meta_3762`).

## Next

Test the rewrite catalogue {delete + redirect, (s|A)&(s|B) -> s|(A&B), repeated leaf in an AND
tree} on every non-read-2 lift fixed point, including the 7-vertex tree of `L_meta_3762`. If it
always shrinks the circuit on 4-cycle-free graphs, try to prove that local statement directly (a
construction, not a size lower bound).
