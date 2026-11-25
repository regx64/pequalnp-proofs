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

# Iteration 2

## Forest case (`Forest2584.lean`, builds locally, axioms `propext`, `Classical.choice`, `Quot.sound`)

* `Scratch.ReadMono.isReadK_two_of_one`: `IsReadK n C 1 -> IsReadK n C 2` for every circuit (the
  capped vector sets at cap 1 and cap 2 agree on vectors with entries at most 1).
* `Scratch.Forest2584.forest_case`: when the incidence graph is acyclic, every `IsAO2` circuit for
  the incidence function has a no-larger `IsAO2` circuit for it that is read-2. It combines the
  checked `L_meta_3525` (forests: size >= E + tau - 1) with the checked `L_meta_7684` (read-1 star
  cover of size E + |A| + |B| - 1), through a least vertex cover split into its point and line
  halves. This is the lower-bound route on a class where the lower bound is already checked; it
  says nothing about 4-cycle-free graphs with cycles.

## Sampling on 7 and 8 vertices (`tools/sampler.py`, `sampling-n7-n8.txt`)

CaDiCaL with random seeds and blocking clauses, 200 circuits per (graph, size), sizes from least
+ 1 to least + 3 (least taken as E + tau - 1 for these forests and cycles). Each circuit is
lift-normalized; every normalized circuit of read >= 3 is tested for two shrinking rewrites
(delete + redirect, `(s|A)&(s|B) -> s|(A&B)`).

* Every normalized read->=3 circuit was shrunk by one of the two rewrites, except one: on the
  double star 0-1,0-2,0-3,0-4,4-5,4-6,4-7 at 11 gates (least 8):
  `w8=OR(0,4) w9=OR(0,7) w10=OR(6,9) w11=AND(8,10) w12=AND(3,11) w13=OR(5,11) w14=AND(8,13)
   w15=OR(2,4) w16=OR(1,15) w17=AND(14,16) w18=OR(12,17)`, edge {4,6} read 3 times.
  Absorption `u & (a | (u & t)) = u & (a | t)` lets `w13` read `w10` instead of `w11`
  (w13's only reader is w14 = AND(w8, w13), and w11 = AND(w8, w10)): same size, read-2.
  So a shrinking rewrite is not always available; a size-neutral rewire is needed too.

## Next

Rewriting system {lift, delete + redirect, distributive, absorption rewire}: none increases size.
Test whether greedy application always ends at a read-2 circuit on 4-cycle-free graphs; then look
for a potential function that every move lowers.

# Iteration 3

## Rewriting system (`tools/rewrite.py`, `rewriting-results.txt`)

Moves, none of which increases size: lift; delete a gate and redirect its reads to an earlier
wire; `(s|A)&(s|B) -> s|(A&B)` when both ORs are read only there; absorb (`g = u & v`, an OR `o`
on a private OR path from `v` reads `h = u & t`: `o` reads `t` instead).

* Termination (on paper): each move strictly lowers (size, number of gates outside the top OR
  tree, sum over operand slots of the operand's depth) lexicographically.
* Computed: on every lift-normalized read->=3 circuit found (exhaustive sets on 4 to 6 vertices,
  samples on 7 and 8 vertices; about 1,500 circuits), greedy application ends at read-2.
* `tools/classify.py`: in the 681 bad circuits of 0-1,0-2,0-3,0-4,1-5 at 8 gates, the redirect is
  always "replace a gate by one of its own operands" (an operand redundant in context).
* Limit of the method: every small 4-cycle-free graph has only star-like least circuits with no
  junk AND, so the statement is trivially true there; graphs with many cycles (Heawood, the
  subdivided K4) were out of reach of the SAT sampler (no sample in 10 to 15 minutes).

## Lemma R2 (`R2.lean`, builds locally, axioms `propext`, `Classical.choice`, `Quot.sound`)

`Scratch.R2.read2_of_structure`: for ANY simple graph, an `IsAO2` circuit for its edge function is
read-2 if (S) no AND gate is true at an input with exactly one variable on, and (T) every AND
gate reached from the output through OR gates has operands whose OR closures contain only AND
gates whose operands' OR closures contain no AND gate. No lower bound and no 4-cycle condition is
used. Computed check (`tools/r2check.py`, about 20,000 circuits): no violation; each of the three
conditions TopForm / (S) / junk depth <= 1 can be dropped only at the cost of read->=3 examples.

Reduction obtained: L-meta-2584 follows from "every AO2 circuit for the incidence function has a
no-larger AO2 circuit satisfying (S) and (T)". That normal-form statement is at least as strong as
L-meta-2584 and is not known; (S) is close to the desk's L-meta-3321, (T) is new.

# Iteration 4: the Fano incidence graph (Heawood graph) and Lemma V

Question: does the incidence graph of the Fano plane (the Heawood graph: 14 vertices, 21 edges,
tau = 7, 4-cycle-free) have an `IsAO2` circuit with fewer than its 27-gate star cover? A yes would
be the first 4-cycle-free graph where the lower bound E + tau - 1 fails, i.e. the first instance
where L-meta-2584 has content beyond the lower bound (iteration 1, E2/E3).

## Block normal form used by every encoding (tools/fano/)

A least circuit can be taken in TopForm (checked `L_meta_5779`). In a least TopForm circuit the
checked `L_meta_1498` (a) gives: every gate below F other than the output has exactly one reader,
an OR gate below F. Hence the gates below F are the "tops" (AND gates below F) and an OR tree over
them; a top reads no gate below F (its reader would be an AND), and a gate not below F ("inner")
reads no gate below F. So the order [inner gates] [tops] [OR tree] is topological, and the OR tree
can be replaced by the chain T1 | T2 | ... | Tt (same size, every other gate unchanged). The
checked `L_meta_1490` (first conjunct) gives, for every top, disjoint "sides" (inputs reachable
from each operand through OR gates only), every cross pair an edge, one side of size <= 1.
Further WLOG choices (each from least-ness: deletable or reorderable gates): distinct operands in
increasing order, every inner gate read, greedy order inside the inner block, tops strictly
increasing, every inner gate true on some maximal zero. Size: m inner + t tops + (t - 1) chain.
Rows: minterms (edges) and maximal zeros (maximal independent sets), which determine a monotone
function; optional implied rows (`--extra`): singletons and non-edge pairs, where every top is 0.

Checks of the encoding: the hand-built 27-gate star cover `star27.txt` passes `verify.py` (right
on all 2^14 inputs, C1/C2/C4, read-1) and, pinned with `--fix`, satisfies every encoding (SAT in
0.1 s); on small graphs (C6, spider, trees) the encodings reproduce the exhaustive least sizes.

## Prior work found upstream after these were derived

The two lemmas below were derived independently in this iteration, and then found to be
essentially already checked upstream, in the `TopForm` vocabulary (`junk` = inner AND gates,
`centreless` = t0, `starEdges` / `Ustar` = E_real / E_virt, `lam` = merging gates in a centre's
side cone, `orN \ lam` = X):
* `L_meta_4183` (NoFourCycle, least, TopForm):
  E + |tops \ centreless| + 2 |centreless| + |junk| + |orN \ lam| <= size + |Ustar| + 1.
  This is Lemma V, before the step |tops \ centreless| >= tau - tau(Ustar).
* `L_meta_1876` (girth >= 5, least, TopForm, junk empty): Ustar is empty. With `L_meta_4183` this is
  the pure-OR lemma for least TopForm circuits on girth >= 5 graphs.
* `L_meta_3760` (bipartite, NoFourCycle, least): |junk| != 1.
So the new content here is only: the pure-OR lemma for ALL AND-depth-1 circuits (no least-ness,
no girth condition), the encodings, and the data. For the Heawood search, `L_meta_3760` +
`L_meta_1876` + `L_meta_4183` give: a least circuit with at most 26 gates has at least 2 junk gates
(`topsat4.py --minand 2`).

## Pure-OR lemma (proved here, on paper)

If every AND gate of a monotone fan-in-2 circuit for the edge function of a 4-cycle-free graph
reads only wires whose cones contain no AND gate ("AND depth 1"), the circuit has at least
E + tau - 1 gates.

Proof. Each AND gate (top) is `OR(A) & OR(B)` for input sets A, B. The output is an OR of tops
(an input in the output's OR-expansion would make F true on one vertex). A top below the output
is below F, so A, B are disjoint and A x B is a set of edges; with no 4-cycle, |A| = 1 or |B| = 1:
a star with center v and side S within N(v). Let U_v be the union of the sides at center v and
r_v the number of tops at v. Every edge lies in some star, so sum_v |U_v| >= E and the centers
form a vertex cover, so the number of tops t >= tau. In the OR circuit below the tops, call an OR
gate merging if both operands have nonempty OR-reachable input sets. Processing the OR-cones of
the sides at v in topological order with a union-find on U_v shows at least |U_v| - r_v merging
gates there. A merging gate has at least two OR-reachable inputs, all in N(v) for every center v
whose side cone contains it; two centers would give a 4-cycle, so these gate sets are disjoint.
The OR gates above the tops are at least t - 1. Total: sum_v (|U_v| - r_v) + t + (t - 1)
= sum_v |U_v| + t - 1 >= E + tau - 1.

So a circuit beating the star cover must have an AND gate not below F reading into a top (an
"inner AND"). This is a partial lower bound, not a circular one: it says nothing about circuits
with inner ANDs, which is exactly where L-meta-2584 lives.

## Lemma V (virtual-edge accounting; proved here, on paper; = checked L_meta_4183 up to the tau step)

For a circuit in block normal form for a 4-cycle-free graph, with
* E_real = edges in some top's real star A_k x B_k (A_k, B_k: OR-reachable inputs of the operands),
  E_virt = the other edges (covered only through inner AND gates),
* t0 = tops whose real star is empty (one side has no OR-reachable input),
* X = inner OR gates that are not merging gates inside the OR-cone of a center's side operand,
* mAND = inner AND gates,

  s >= E + tau - 1 + (2 t0 + X + mAND) - (|E_virt| + tau(E_virt)).

Proof: the pure-OR count, applied to the real stars only (the merging-gate argument never needed
the leaves of the OR trees to be inputs), gives s >= sum_v |U_v| + t + t0 + X + mAND - 1, while
E <= sum_v |U_v| + |E_virt| and tau <= (number of centers) + tau(E_virt) <= (t - t0) + tau(E_virt).
With no inner AND, E_virt is empty and Lemma V is the pure-OR lemma.

Encoding (`topsat4.py --lemmaV TAU --exactX`): exact OR-reachable sets, exact real-edge
indicators, exact X, and the cardinality constraint 2|E_virt| - 2 t0 - X - mAND >= E + tau - 1 - s
(using tau(E_virt) <= |E_virt|). A first version of the exact X had a bug (the OR-cone did not
stop at AND gates). It was found because full enumerations with and without the constraint
disagreed: P4 at 6 gates gave 169 circuits without it and 162 with it. After the fix, the counts
agree on every case tried (6 small graphs, 3 values of t each, sizes least to least + 2), so the
constraint excludes no real circuit there.

## Data

* `innerand7.log`: on all 25 connected 4-cycle-free bipartite graphs with at most
  7 vertices, no least block-form circuit has an inner AND (UNSAT for every t). One gate above
  least size, inner-AND circuits exist (P4: `O0,1 A3,4 O0,5 O1,2 A6,7`).
* Stronger form "V+": 2 t0 + X + mAND >= |E_virt| + tau(E_virt) for every block-form circuit
  (inner ANDs never pay for themselves). It held on every inner-AND circuit enumerated (about
  1,500 circuits, 8 graphs, sizes least + 1 and + 2); the minimum payment margin is 0. With Lemma V,
  V+ implies the lower bound, hence L-meta-2584. V+ is open.
* 2-slice relaxation (`topslice.py --slice`: rows of weight <= 2 only) also gives E + tau - 1 on
  P4, P5, the spider and C6. Barrier (from memory, not checked here): for slice functions,
  monotone and non-monotone complexities are close (Berkowitz), and the projective-plane
  incidence test is cheap non-monotonically. So for large planes the 2-slice relaxation cannot
  give E + tau - 1 (about n^{3/2}), and a general proof must use independent sets of size >= 3.
  The bipartite star-complexity relaxation (`--bislice`) is too weak already on P4.
* Literature: Jukna, "On graph complexity" (CPC 2006), Theorem 7.3 proves a size bound |E|/2 for
  monotone FORMULAS (and depth log|E| - 1 for circuits) for triangle-free 4-cycle-free graphs. I
  found no size lower bound of order |E| for monotone CIRCUITS for 4-cycle-free graphs. So the
  E + tau - 1 bound for all 4-cycle-free graphs would be new (about n^{3/2} for projective planes).
* The desk's own sketch for L-meta-2584 names the open part: "a least circuit whose blocks are not
  single stars: such a block must be shown to cost at least a star cover of the edges it accepts".
  That is V+ (in its least-circuit form).

## Heawood (Fano incidence), 26 gates: results so far

Upstream already has `L_meta_1483` (checked): every Monotone2 circuit for the Fano incidence
function has at least 20 gates. So the least size is in [20, 27]; "no circuit below the star
cover" needs UNSAT at every s in 20..26 (each s separately: block form needs least-ness, so a
smaller circuit cannot be padded to 26 gates).

Encodings and verdicts (CaDiCaL 1.x bundled with the Lean toolchain; 4 cores, 4 jobs at once):

| encoding (file) | vars / clauses at s=26 | verdict |
|---|---|---|
| base W1-W4 (`tools/topsat.py base`) | 6,253 / 165,794 | UNKNOWN in 6,600 s |
| + C1/C2/C4 WLOG (`topsat.py wlog`) | 7,722 / 201,674 | UNKNOWN in 6,600 s (DRAT 6 GB, deleted) |
| block form, per t (`topsat2.py`) | 5.0k-6.3k / 174k-195k | t = 1..6: UNKNOWN in 1,800 s each |
| block + implied rows + exact Lemma V (`topsat4.py --extra --lemmaV 7 --exactX`) | 10.7k-28.7k / 114k-405k | t = 13: UNSAT 0.4 s; t = 12: UNSAT 14.1 s; t = 1..11: UNKNOWN in 1,800 s each |

Sanity: s = 27, t = 7 (the star cover exists) was UNKNOWN in 1,800 s (block form) and in 1,500 s
(with implied rows), but SAT in 0.1 s with the star cover pinned (`--fix star27.txt`). So the
solver, not the encoding, is the limit at this size. A timeout is recorded as UNKNOWN, never as UNSAT.

Benchmark where everything closes: C8 (8 vertices). Base encoding at s = 11 had been UNKNOWN in
811 s; the block form closes s = 7..10 for every t (`data-fano/c8_block.txt`), the hardest case in
144 s, so the least size of C8 is 11 = E + tau - 1. On C8 the gain comes from the block form; Lemma
V changes the times little (127.5 s vs 144 s for t = 1).

Status: for the Fano incidence graph at 26 gates the answer is UNKNOWN. Proved: no 26-gate
least circuit with 12 or 13 tops. Running: t = 11, 10, 9 with at least 2 junk gates (`--minand 2`,
justified by `L_meta_3760` + `L_meta_1876` + `L_meta_4183`), 7,200 s each; t = 8 with 3,600 s.
