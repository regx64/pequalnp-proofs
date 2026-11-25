import Mathlib
import PEqualNP.Defs

/-!
# Lemma R2: a structural sufficient condition for READ-2

Part 1: gate-by-gate formulas for wire values and for `ReadK.readVectors`, for circuits whose
gates read only earlier wires.
-/

namespace Scratch.R2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
  PEqualNP.MetaComplexity.NestedCover

/-! ## A fold that appends one entry per gate -/

section Fold
variable {α : Type} (f : List α → Gate → α)

def stepF (acc : List α) (g : Gate) : List α := acc ++ [f acc g]

theorem foldl_stepF_length (gs : List Gate) (init : List α) :
    (gs.foldl (stepF f) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, stepF, List.length_append]; simp; omega

theorem foldl_stepF_getD_lt (gs : List Gate) (init : List α) (i : ℕ) (d : α)
    (hi : i < init.length) : (gs.foldl (stepF f) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [stepF]; omega)]
    simp only [stepF, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_stepF_take_append (gs : List Gate) (init : List α) (j : ℕ) (hj : j < gs.length) :
    (gs.take (j + 1)).foldl (stepF f) init =
      stepF f ((gs.take j).foldl (stepF f) init) (gs[j]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
  rfl

theorem foldl_stepF_getD_new (gs : List Gate) (init : List α) (j : ℕ) (d : α)
    (hj : j < gs.length) :
    (gs.foldl (stepF f) init).getD (init.length + j) d =
      f ((gs.take j).foldl (stepF f) init) (gs[j]) := by
  have hsplit : gs = gs.take (j + 1) ++ gs.drop (j + 1) := (List.take_append_drop _ _).symm
  have hlen : ((gs.take (j + 1)).foldl (stepF f) init).length = init.length + (j + 1) := by
    rw [foldl_stepF_length, List.length_take]; omega
  conv_lhs => rw [hsplit, List.foldl_append]
  rw [foldl_stepF_getD_lt f _ _ _ _ (by omega), foldl_stepF_take_append f gs init j hj]
  have hlen' : ((gs.take j).foldl (stepF f) init).length = init.length + j := by
    rw [foldl_stepF_length, List.length_take]; omega
  simp only [stepF]
  rw [← hlen', List.getD_append_right _ _ _ _ (le_refl _)]
  simp

/-- Entries below the length of a prefix of the fold are already final. -/
theorem foldl_stepF_getD_prefix (gs : List Gate) (init : List α) (j : ℕ) (i : ℕ) (d : α)
    (hj : j ≤ gs.length) (hi : i < init.length + j) :
    (gs.foldl (stepF f) init).getD i d = ((gs.take j).foldl (stepF f) init).getD i d := by
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop _ _).symm
  conv_lhs => rw [hsplit, List.foldl_append]
  rw [foldl_stepF_getD_lt f _ _ _ _ (by rw [foldl_stepF_length, List.length_take]; omega)]

end Fold

/-! ## Wire values -/

def valStep (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl (stepF valStep) x := rfl

/-- The value of wire `w` of `C` at the input `x` on `n` inputs. -/
def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val n C x i = x ⟨i, hi⟩ := by
  unfold val
  rw [wires_eq, foldl_stepF_getD_lt _ _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem val_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val n C x i) := by
  have hg : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  unfold val
  rw [wires_eq]
  have hlen : (List.ofFn x).length = n := by simp
  rw [show n + j = (List.ofFn x).length + j by rw [hlen], foldl_stepF_getD_new _ _ _ _ _ hj]
  simp only [valStep, hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < n + j := hRB j hj i (by rw [hg]; exact hi)
  rw [foldl_stepF_getD_prefix _ _ _ j i _ hj.le (by rw [hlen]; exact hlt)]

/-! ## Read vectors -/

/-- One read-vector step, reading the sets of earlier wires through `r`. -/
def rvStepF (S : List ℕ) (k : ℕ) (r : ℕ → List (List ℕ)) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map r).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map r).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def rvStep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  rvStepF S k (fun i => R.getD i []) g

theorem readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (stepF (rvStep S k)) ((List.range n).map (leafVectors S k)) := by
  unfold readVectors stepF rvStep rvStepF
  rfl

theorem rvStepF_congr (S : List ℕ) (k : ℕ) (r r' : ℕ → List (List ℕ)) (g : Gate)
    (h : ∀ i ∈ g.inputs, r i = r' i) : rvStepF S k r g = rvStepF S k r' g := by
  have : g.inputs.map r = g.inputs.map r' := List.map_congr_left h
  unfold rvStepF; rw [this]

/-- The read-vector set of wire `w`. -/
def RV (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

theorem RV_input {n : ℕ} (C : Circuit) (S : List ℕ) (k i : ℕ) (hi : i < n) :
    RV n C S k i = leafVectors S k i := by
  unfold RV
  rw [readVectors_eq, foldl_stepF_getD_lt _ _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem RV_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (S : List ℕ) (k : ℕ) (j : ℕ)
    (hj : j < C.gates.length) :
    RV n C S k (n + j) = rvStepF S k (RV n C S k) (gateAt C j) := by
  have hg : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  have hlen : ((List.range n).map (leafVectors S k)).length = n := by simp
  have e : RV n C S k (n + j) = rvStep S k
      ((C.gates.take j).foldl (stepF (rvStep S k)) ((List.range n).map (leafVectors S k)))
      (C.gates[j]) := by
    unfold RV
    rw [readVectors_eq, show n + j = ((List.range n).map (leafVectors S k)).length + j by rw [hlen],
      foldl_stepF_getD_new _ _ _ _ _ hj]
  rw [e, hg]
  show rvStepF S k (fun i => ((C.gates.take j).foldl (stepF (rvStep S k))
    ((List.range n).map (leafVectors S k))).getD i []) (C.gates[j]) = _
  apply rvStepF_congr
  intro i hi
  have hlt : i < n + j := hRB j hj i (by rw [hg]; exact hi)
  unfold RV
  rw [readVectors_eq, foldl_stepF_getD_prefix _ _ _ j i _ hj.le (by rw [hlen]; exact hlt)]


/-! ## Part 2: the descent -/

section Descent

variable {n : ℕ} (C : Circuit)

/-- `m` is reached from wire `w` through OR gates only (`w` itself included). -/
inductive OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop
  | refl (w : ℕ) : OrR n C w w
  | step (j i m : ℕ) : j < C.gates.length → (gateAt C j).op = GateOp.or →
      i ∈ (gateAt C j).inputs → OrR n C i m → OrR n C (n + j) m

/-- Wire `w` is the wire of an AND gate. -/
def IsAndW (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ j, w = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.and

/-- No AND gate is reached from `w` through OR gates. -/
def NoAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop := ∀ m, OrR n C w m → ¬ IsAndW n C m

/-- Every AND gate reached from `w` through OR gates has operands that reach no AND gate. -/
def JunkOK (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ m, OrR n C w m → ∀ j, m = n + j → j < C.gates.length → (gateAt C j).op = GateOp.and →
    ∀ i ∈ (gateAt C j).inputs, NoAnd n C i

/-- Every AND gate reached from `w` through OR gates has operands satisfying `JunkOK`. -/
def TopOK (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ m, OrR n C w m → ∀ j, m = n + j → j < C.gates.length → (gateAt C j).op = GateOp.and →
    ∀ i ∈ (gateAt C j).inputs, JunkOK n C i

theorem gate_mem (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem two_inputs (hAO : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ i0 i1, (gateAt C j).inputs = [i0, i1] ∧ i0 < n + j ∧ i1 < n + j := by
  have hl := hAO.2.2 _ (gate_mem C j hj)
  match h : (gateAt C j).inputs, hl with
  | [i0, i1], _ =>
    refine ⟨i0, i1, rfl, hAO.2.1 j hj i0 (by rw [h]; simp), hAO.2.1 j hj i1 (by rw [h]; simp)⟩

theorem and_or (hAO : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := hAO.1 _ (gate_mem C j hj)

theorem val_out_of_range (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    val n C x w = false := by
  unfold val
  rw [List.getD_eq_default]
  rw [wires_eq, foldl_stepF_length]; simpa using hw

theorem mem_foldl_insertNew_of {L A : List (List ℕ)} {v : List ℕ} (h : v ∈ A ∨ v ∈ L) :
    v ∈ L.foldl insertNew A := by
  induction L generalizing A with
  | nil => simpa using h
  | cons x L ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left; unfold insertNew; split_ifs <;> simp [h]
    · rcases List.mem_cons.mp h with rfl | h
      · left; unfold insertNew; split_ifs with h' <;> simp [h']
      · right; exact h

theorem mem_andStep_of {k : ℕ} {A B : List (List ℕ)} {u v : List ℕ} (hu : u ∈ A) (hv : v ∈ B) :
    capAdd k u v ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of; right
  simp only [List.mem_flatMap, List.mem_map]; exact ⟨u, hu, v, hv, rfl⟩

variable (S : List ℕ)

theorem RV_or_mem (hAO : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (u : List ℕ)
    (hu : u ∈ RV n C S 2 i) : u ∈ RV n C S 2 (n + j) := by
  rw [RV_gate C hAO.2.1 S 2 j hj]
  obtain ⟨i0, i1, hin, -, -⟩ := two_inputs C hAO j hj
  unfold rvStepF; rw [hop, hin]
  rw [hin] at hi
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact mem_foldl_insertNew_of (Or.inl (mem_foldl_insertNew_of (Or.inr hu)))
  · exact mem_foldl_insertNew_of (Or.inr hu)

theorem RV_and_mem (hAO : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (i0 i1 : ℕ) (hin : (gateAt C j).inputs = [i0, i1])
    (u v : List ℕ) (hu : u ∈ RV n C S 2 i0) (hv : v ∈ RV n C S 2 i1) :
    capAdd 2 (capAdd 2 (S.map fun _ => 0) u) v ∈ RV n C S 2 (n + j) := by
  rw [RV_gate C hAO.2.1 S 2 j hj]
  unfold rvStepF; rw [hop, hin]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  exact mem_andStep_of (mem_andStep_of (List.mem_singleton_self _) hu) hv

theorem val_or (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (i0 i1 : ℕ)
    (hin : (gateAt C j).inputs = [i0, i1]) :
    val n C x (n + j) = (val n C x i0 || val n C x i1) := by
  rw [val_gate C hAO.2.1 x j hj, hop, hin]; simp [GateOp.eval]

theorem val_and (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (i0 i1 : ℕ)
    (hin : (gateAt C j).inputs = [i0, i1]) :
    val n C x (n + j) = (val n C x i0 && val n C x i1) := by
  rw [val_gate C hAO.2.1 x j hj, hop, hin]; simp [GateOp.eval]

end Descent

section Edge

variable {n : ℕ} (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (p q : ℕ) (hp : p < n)
  (hq : q < n) (hpq : p ≠ q)

/-- The input with `p` and `q` on, and the two singletons. -/
def xe (p q : ℕ) : Fin n → Bool := fun t => decide (t.val = p ∨ t.val = q)
def xs (p : ℕ) : Fin n → Bool := fun t => decide (t.val = p)

include hAO hp hq hpq in
/-- Descent through OR gates only: a unit vector, and the singleton input of its vertex is
accepted. -/
theorem descent0 : ∀ w, w < n + C.gates.length → NoAnd n C w → val n C (xe p q) w = true →
    (val n C (xs p) w = true ∧ [1, 0] ∈ RV n C [p, q] 2 w) ∨
    (val n C (xs q) w = true ∧ [0, 1] ∈ RV n C [p, q] 2 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hno hval
  by_cases hin : w < n
  · rw [val_input C _ w hin] at hval
    simp only [xe, decide_eq_true_eq] at hval
    rw [RV_input C _ 2 w hin]
    rcases hval with rfl | rfl
    · left; refine ⟨by rw [val_input C _ _ hin]; simp [xs], ?_⟩
      simp [leafVectors, hpq.symm]
    · right; refine ⟨by rw [val_input C _ _ hin]; simp [xs], ?_⟩
      simp [leafVectors, hpq]
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hop : (gateAt C j).op = GateOp.or := by
      rcases and_or C hAO j hj with h | h
      · exact absurd ⟨j, rfl, hj, h⟩ (hno _ (OrR.refl _))
      · exact h
    obtain ⟨i0, i1, hins, h0, h1⟩ := two_inputs C hAO j hj
    rw [val_or C hAO _ j hj hop i0 i1 hins] at hval
    have hsub : ∀ i ∈ (gateAt C j).inputs, NoAnd n C i := fun i hi m hm =>
      hno m (OrR.step j i m hj hop hi hm)
    have key : ∀ i, i ∈ (gateAt C j).inputs → i < n + j → val n C (xe p q) i = true →
        (val n C (xs p) (n + j) = true ∧ [1, 0] ∈ RV n C [p, q] 2 (n + j)) ∨
        (val n C (xs q) (n + j) = true ∧ [0, 1] ∈ RV n C [p, q] 2 (n + j)) := by
      intro i hi hlt hv
      have hi' : i = i0 ∨ i = i1 := by rw [hins] at hi; simpa using hi
      rcases ih i hlt (by omega) (hsub i hi) hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
      · left; refine ⟨?_, RV_or_mem C _ hAO j hj hop i hi _ hv2⟩
        rw [val_or C hAO _ j hj hop i0 i1 hins]; rcases hi' with rfl | rfl <;> simp [hv1]
      · right; refine ⟨?_, RV_or_mem C _ hAO j hj hop i hi _ hv2⟩
        rw [val_or C hAO _ j hj hop i0 i1 hins]; rcases hi' with rfl | rfl <;> simp [hv1]
    rcases Bool.or_eq_true_iff.mp hval with h | h
    · exact key i0 (by rw [hins]; simp) h0 h
    · exact key i1 (by rw [hins]; simp) h1 h

theorem capAdd_two_vals (a b c d : ℕ) :
    capAdd 2 (capAdd 2 ([p, q].map fun _ => 0) [a, b]) [c, d] =
      [min (min a 3 + c) 3, min (min b 3 + d) 3] := by
  simp [capAdd]

include hAO hp hq hpq in
/-- Descent through junk: a vector with entries at most 1. -/
theorem descent1 (hsing : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      val n C (xs p) (n + j) = false ∧ val n C (xs q) (n + j) = false) :
    ∀ w, w < n + C.gates.length → JunkOK n C w → val n C (xe p q) w = true →
    ∃ a b, [a, b] ∈ RV n C [p, q] 2 w ∧ a ≤ 1 ∧ b ≤ 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hjk hval
  by_cases hin : w < n
  · have hno : NoAnd n C w := by
      intro m hm hm'
      obtain ⟨j, rfl, -, -⟩ := hm'
      cases hm with
      | refl => omega
      | step j' i m hj' _ _ _ => omega
    rcases descent0 C hAO p q hp hq hpq w hw hno hval with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨1, 0, h, le_refl _, Nat.zero_le _⟩
    · exact ⟨0, 1, h, Nat.zero_le _, le_refl _⟩
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨i0, i1, hins, h0, h1⟩ := two_inputs C hAO j hj
    rcases and_or C hAO j hj with hop | hop
    · -- a junk AND: its operands reach no AND
      have hn0 : NoAnd n C i0 := hjk _ (OrR.refl _) j rfl hj hop i0 (by rw [hins]; simp)
      have hn1 : NoAnd n C i1 := hjk _ (OrR.refl _) j rfl hj hop i1 (by rw [hins]; simp)
      rw [val_and C hAO _ j hj hop i0 i1 hins, Bool.and_eq_true] at hval
      obtain ⟨hs1, hs2⟩ := hsing j hj hop
      rw [val_and C hAO _ j hj hop i0 i1 hins] at hs1 hs2
      rcases descent0 C hAO p q hp hq hpq i0 (by omega) hn0 hval.1 with ⟨a0, u0⟩ | ⟨a0, u0⟩ <;>
      rcases descent0 C hAO p q hp hq hpq i1 (by omega) hn1 hval.2 with ⟨a1, u1⟩ | ⟨a1, u1⟩
      · simp [a0, a1] at hs1
      · have := RV_and_mem C [p, q] hAO j hj hop i0 i1 hins _ _ u0 u1
        rw [capAdd_two_vals] at this
        exact ⟨_, _, this, by norm_num, by norm_num⟩
      · have := RV_and_mem C [p, q] hAO j hj hop i0 i1 hins _ _ u0 u1
        rw [capAdd_two_vals] at this
        exact ⟨_, _, this, by norm_num, by norm_num⟩
      · simp [a0, a1] at hs2
    · rw [val_or C hAO _ j hj hop i0 i1 hins] at hval
      have hsub : ∀ i ∈ (gateAt C j).inputs, JunkOK n C i := fun i hi m hm =>
        hjk m (OrR.step j i m hj hop hi hm)
      have key : ∀ i, i ∈ (gateAt C j).inputs → i < n + j → val n C (xe p q) i = true →
          ∃ a b, [a, b] ∈ RV n C [p, q] 2 (n + j) ∧ a ≤ 1 ∧ b ≤ 1 := by
        intro i hi hlt hv
        obtain ⟨a, b, h, ha, hb⟩ := ih i hlt (by omega) (hsub i hi) hv
        exact ⟨a, b, RV_or_mem C _ hAO j hj hop i hi _ h, ha, hb⟩
      rcases Bool.or_eq_true_iff.mp hval with h | h
      · exact key i0 (by rw [hins]; simp) h0 h
      · exact key i1 (by rw [hins]; simp) h1 h

include hAO hp hq hpq in
/-- Descent from a wire whose OR closure ends in tops: a vector with entries at most 2,
provided neither singleton input is accepted. -/
theorem descent2 (hsing : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      val n C (xs p) (n + j) = false ∧ val n C (xs q) (n + j) = false) :
    ∀ w, w < n + C.gates.length → TopOK n C w → val n C (xs p) w = false →
    val n C (xs q) w = false → val n C (xe p q) w = true →
    ∃ a b, [a, b] ∈ RV n C [p, q] 2 w ∧ a ≤ 2 ∧ b ≤ 2 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw htop hsp hsq hval
  by_cases hin : w < n
  · rw [val_input C _ w hin] at hval hsp hsq
    simp only [xe, xs, decide_eq_true_eq, decide_eq_false_iff_not] at hval hsp hsq
    tauto
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨i0, i1, hins, h0, h1⟩ := two_inputs C hAO j hj
    rcases and_or C hAO j hj with hop | hop
    · have hk0 : JunkOK n C i0 := htop _ (OrR.refl _) j rfl hj hop i0 (by rw [hins]; simp)
      have hk1 : JunkOK n C i1 := htop _ (OrR.refl _) j rfl hj hop i1 (by rw [hins]; simp)
      rw [val_and C hAO _ j hj hop i0 i1 hins, Bool.and_eq_true] at hval
      obtain ⟨a, b, ha, ha1, hb1⟩ := descent1 C hAO p q hp hq hpq hsing i0 (by omega) hk0 hval.1
      obtain ⟨c, d, hc, hc1, hd1⟩ := descent1 C hAO p q hp hq hpq hsing i1 (by omega) hk1 hval.2
      have := RV_and_mem C [p, q] hAO j hj hop i0 i1 hins _ _ ha hc
      rw [capAdd_two_vals] at this
      exact ⟨_, _, this, by omega, by omega⟩
    · rw [val_or C hAO _ j hj hop i0 i1 hins] at hval hsp hsq
      have hsub : ∀ i ∈ (gateAt C j).inputs, TopOK n C i := fun i hi m hm =>
        htop m (OrR.step j i m hj hop hi hm)
      simp only [Bool.or_eq_false_iff] at hsp hsq
      rcases Bool.or_eq_true_iff.mp hval with h | h
      · obtain ⟨a, b, hab, ha, hb⟩ := ih i0 h0 (by omega) (hsub i0 (by rw [hins]; simp))
          hsp.1 hsq.1 h
        exact ⟨a, b, RV_or_mem C _ hAO j hj hop i0 (by rw [hins]; simp) _ hab, ha, hb⟩
      · obtain ⟨a, b, hab, ha, hb⟩ := ih i1 h1 (by omega) (hsub i1 (by rw [hins]; simp))
          hsp.2 hsq.2 h
        exact ⟨a, b, RV_or_mem C _ hAO j hj hop i1 (by rw [hins]; simp) _ hab, ha, hb⟩

include hAO hp hq hpq in
theorem edge_read2 (hsing : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      val n C (xs p) (n + j) = false ∧ val n C (xs q) (n + j) = false)
    (htop : TopOK n C C.output) (hop : val n C (xs p) C.output = false)
    (hoq : val n C (xs q) C.output = false) (hoe : val n C (xe p q) C.output = true) :
    readsAtMost C n [p, q] 2 = true := by
  have hw : C.output < n + C.gates.length := by
    by_contra h; rw [val_out_of_range C _ _ (by omega)] at hoe; exact absurd hoe (by simp)
  obtain ⟨a, b, hab, ha, hb⟩ := descent2 C hAO p q hp hq hpq hsing C.output hw htop hop hoq hoe
  unfold readsAtMost
  apply List.any_eq_true.mpr
  refine ⟨[a, b], hab, ?_⟩
  simp [ha, hb]

end Edge

/-! ## Part 3: from edges to `IsReadK` -/

section Main

theorem setList_pair {n : ℕ} (u v : Fin n) (h : u ≠ v) :
    ∃ a b, setList ({u, v} : Finset (Fin n)) = [a, b] ∧
      ((a = u.val ∧ b = v.val) ∨ (a = v.val ∧ b = u.val)) := by
  classical
  set L := (List.finRange n).filter (fun i => decide (i ∈ ({u, v} : Finset (Fin n)))) with hL
  have hnd : L.Nodup := (List.nodup_finRange n).filter _
  have hmem : ∀ i, i ∈ L ↔ i = u ∨ i = v := by intro i; simp [hL]
  have htf : L.toFinset = {u, v} := by ext i; simp [hmem]
  have hlen : L.length = 2 := by
    rw [← List.toFinset_card_of_nodup hnd, htf, Finset.card_pair h]
  have hsl : setList ({u, v} : Finset (Fin n)) = L.map Fin.val := rfl
  match hm : L, hlen with
  | [c, d], _ =>
    have hc := (hmem c).mp (by simp)
    have hd := (hmem d).mp (by simp)
    have hcd : c ≠ d := by simpa using hnd
    refine ⟨c.val, d.val, by rw [hsl]; rfl, ?_⟩
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact absurd rfl hcd
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hcd

theorem prime_is_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hF : ∀ x, circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (S : Finset (Fin n)) (hS : IsPrimeImplicant n C S) :
    ∃ u v, G.Adj u v ∧ S = {u, v} := by
  classical
  obtain ⟨h1, h2⟩ := hS
  rw [hF, decide_eq_true_eq] at h1
  obtain ⟨u, v, hadj, hu, hv⟩ := h1
  simp only [setInput, decide_eq_true_eq] at hu hv
  refine ⟨u, v, hadj, ?_⟩
  by_contra hne
  have hsub : ({u, v} : Finset (Fin n)) ⊂ S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption,
      fun h => hne h.symm⟩
  have := h2 _ (Finset.mem_ssubsets.mpr hsub)
  rw [hF] at this
  simp only [decide_eq_false_iff_not, not_exists, not_and] at this
  exact this u v hadj (by simp [setInput]) (by simp [setInput])

/-- **Lemma R2.** An AO2 circuit for the edge function of any simple graph is READ-2 when
(S) no AND gate is true at an input with exactly one variable on, and (T) every AND gate reached
from the output through OR gates (a top) has operands whose OR closures contain only AND gates
(junk) whose operands' OR closures contain no AND gate. -/
theorem read2_of_structure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : ∀ x, circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hsing : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ t : Fin n, val n C (fun s => decide (s = t)) (n + j) = false)
    (htop : TopOK n C C.output) : IsReadK n C 2 := by
  classical
  intro S hS
  obtain ⟨u, v, hadj, rfl⟩ := prime_is_edge G C hF S hS
  have huv : u ≠ v := G.ne_of_adj hadj
  obtain ⟨a, b, hab, hor⟩ := setList_pair u v huv
  rw [hab]
  have hval : ∀ x : Fin n → Bool, val n C x C.output = circuitFun n C x := fun _ => rfl
  have hsingle : ∀ c : Fin n, val n C (xs c.val) C.output = false := by
    intro c
    rw [hval, hF]
    simp only [xs, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    intro u' v' had h1 h2
    exact G.ne_of_adj had (Fin.ext (h1.trans h2.symm))
  have hxs : ∀ c : Fin n, (xs c.val : Fin n → Bool) = fun s => decide (s = c) := by
    intro c; funext s; simp [xs, Fin.ext_iff]
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine edge_read2 C hAO u.val v.val u.2 v.2 (fun h => huv (Fin.ext h))
      (fun j hj hop => ⟨by rw [hxs u]; exact hsing j hj hop u, by rw [hxs v]; exact hsing j hj hop v⟩)
      htop (hsingle u) (hsingle v) ?_
    rw [hval, hF, decide_eq_true_eq]
    exact ⟨u, v, hadj, by simp [xe], by simp [xe]⟩
  · refine edge_read2 C hAO v.val u.val v.2 u.2 (fun h => huv (Fin.ext h).symm)
      (fun j hj hop => ⟨by rw [hxs v]; exact hsing j hj hop v, by rw [hxs u]; exact hsing j hj hop u⟩)
      htop (hsingle v) (hsingle u) ?_
    rw [hval, hF, decide_eq_true_eq]
    exact ⟨u, v, hadj, by simp [xe], by simp [xe]⟩

end Main

end Scratch.R2
