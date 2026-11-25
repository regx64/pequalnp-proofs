import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_3525
import PEqualNP.Outside.L_meta_7684

/-!
# READ-1 implies READ-2

For the capped count-vector recursion `PEqualNP.ReadK.readVectors`: every vector with all entries
at most 1 that the recursion at `k = 1` produces for a wire is also produced at `k = 2`.
-/

namespace Scratch.ReadMono

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

/-- All entries at most 1. -/
def Good (u : List ℕ) : Prop := ∀ a ∈ u, a ≤ 1

theorem mem_insertNew {A : List (List ℕ)} {x v : List ℕ} :
    v ∈ insertNew A x ↔ v ∈ A ∨ v = x := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl) <;> assumption
  · simp

theorem mem_foldl_insertNew (L : List (List ℕ)) :
    ∀ (A : List (List ℕ)) (v : List ℕ), v ∈ L.foldl insertNew A ↔ v ∈ A ∨ v ∈ L := by
  induction L with
  | nil => intro A v; simp
  | cons x L ih =>
    intro A v
    rw [List.foldl_cons, ih, mem_insertNew]
    simp only [List.mem_cons]
    tauto

theorem mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩; exact ⟨u, hu, w, hw, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩; exact ⟨u, hu, w, hw, rfl⟩

theorem capAdd_length {k : ℕ} {u w : List ℕ} (h : u.length = w.length) :
    (capAdd k u w).length = u.length := by
  unfold capAdd; simp [List.length_zipWith, h]

/-- A good sum of two equal-length vectors comes from two good vectors, and the caps at `1` and
`2` agree on it. -/
theorem good_of_capAdd : ∀ (u w : List ℕ), u.length = w.length → Good (capAdd 1 u w) →
    Good u ∧ Good w ∧ capAdd 2 u w = capAdd 1 u w := by
  intro u
  induction u with
  | nil => intro w h _; cases w <;> simp_all [Good, capAdd]
  | cons x u ih =>
    intro w h hg
    cases w with
    | nil => simp at h
    | cons y w =>
      simp only [List.length_cons, add_left_inj] at h
      have hx : min (x + y) (1 + 1) ≤ 1 := hg _ (by simp [capAdd])
      have hrest : Good (capAdd 1 u w) := fun a ha => hg a (by simp [capAdd] at ha ⊢; exact Or.inr ha)
      obtain ⟨gu, gw, he⟩ := ih w h hrest
      have hxy : x + y ≤ 1 := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro a ha; simp at ha; rcases ha with rfl | ha; · omega
        exact gu a ha
      · intro a ha; simp at ha; rcases ha with rfl | ha; · omega
        exact gw a ha
      · have e2 : capAdd 2 (x :: u) (y :: w) = min (x + y) (2 + 1) :: capAdd 2 u w := rfl
        have e1 : capAdd 1 (x :: u) (y :: w) = min (x + y) (1 + 1) :: capAdd 1 u w := rfl
        rw [e2, e1, he]; congr 1; omega

/-- The invariant between the sets at caps 1 and 2: every vector has length `m`, and every good
vector at cap 1 is present at cap 2. -/
def Inv (m : ℕ) (A1 A2 : List (List ℕ)) : Prop :=
  (∀ u ∈ A1, u.length = m) ∧ (∀ u ∈ A2, u.length = m) ∧ ∀ u ∈ A1, Good u → u ∈ A2

theorem inv_nil (m : ℕ) : Inv m [] [] := by simp [Inv]

theorem inv_andStep {m : ℕ} {A1 A2 B1 B2 : List (List ℕ)} (hA : Inv m A1 A2) (hB : Inv m B1 B2) :
    Inv m (andStep 1 A1 B1) (andStep 2 A2 B2) := by
  obtain ⟨la1, la2, ga⟩ := hA
  obtain ⟨lb1, lb2, gb⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_andStep.mp hv
    rw [capAdd_length (by rw [la1 u hu, lb1 w hw])]; exact la1 u hu
  · intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_andStep.mp hv
    rw [capAdd_length (by rw [la2 u hu, lb2 w hw])]; exact la2 u hu
  · intro v hv hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_andStep.mp hv
    obtain ⟨gu, gw, he⟩ := good_of_capAdd u w (by rw [la1 u hu, lb1 w hw]) hg
    exact mem_andStep.mpr ⟨u, ga u hu gu, w, gb w hw gw, he.symm⟩

theorem inv_union {m : ℕ} {A1 A2 B1 B2 : List (List ℕ)} (hA : Inv m A1 A2) (hB : Inv m B1 B2) :
    Inv m (B1.foldl insertNew A1) (B2.foldl insertNew A2) := by
  obtain ⟨la1, la2, ga⟩ := hA
  obtain ⟨lb1, lb2, gb⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; rcases (mem_foldl_insertNew _ _ _).mp hv with h | h
    · exact la1 v h
    · exact lb1 v h
  · intro v hv; rcases (mem_foldl_insertNew _ _ _).mp hv with h | h
    · exact la2 v h
    · exact lb2 v h
  · intro v hv hg; rcases (mem_foldl_insertNew _ _ _).mp hv with h | h
    · exact (mem_foldl_insertNew _ _ _).mpr (Or.inl (ga v h hg))
    · exact (mem_foldl_insertNew _ _ _).mpr (Or.inr (gb v h hg))

/-- Two lists of sets related pointwise by `Inv`. -/
def Rel (m : ℕ) (R1 R2 : List (List (List ℕ))) : Prop :=
  R1.length = R2.length ∧ ∀ i, Inv m (R1.getD i []) (R2.getD i [])

theorem rel_ins {m : ℕ} {R1 R2 : List (List (List ℕ))} (h : Rel m R1 R2) (l : List ℕ) :
    List.Forall₂ (Inv m) (l.map fun i => R1.getD i []) (l.map fun i => R2.getD i []) := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons]; exact List.Forall₂.cons (h.2 i) ih

theorem inv_orFold {m : ℕ} : ∀ (L1 L2 : List (List (List ℕ))), List.Forall₂ (Inv m) L1 L2 →
    ∀ (a1 a2 : List (List ℕ)), Inv m a1 a2 →
    Inv m (L1.foldl (fun acc A => A.foldl insertNew acc) a1)
      (L2.foldl (fun acc A => A.foldl insertNew acc) a2) := by
  intro L1 L2 hL
  induction hL with
  | nil => intro a1 a2 h; simpa using h
  | cons hx _ ih => intro a1 a2 h; simp only [List.foldl_cons]; exact ih _ _ (inv_union h hx)

theorem inv_andFold {m : ℕ} : ∀ (L1 L2 : List (List (List ℕ))), List.Forall₂ (Inv m) L1 L2 →
    ∀ (a1 a2 : List (List ℕ)), Inv m a1 a2 →
    Inv m (L1.foldl (andStep 1) a1) (L2.foldl (andStep 2) a2) := by
  intro L1 L2 hL
  induction hL with
  | nil => intro a1 a2 h; simpa using h
  | cons hx _ ih => intro a1 a2 h; simp only [List.foldl_cons]; exact ih _ _ (inv_andStep h hx)

theorem getD_append_single (R : List (List (List ℕ))) (x : List (List ℕ)) (i : ℕ) :
    (R ++ [x]).getD i [] = if i < R.length then R.getD i [] else if i = R.length then x else [] := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem rel_step {m : ℕ} (S : List ℕ) (hS : S.length = m) {R1 R2 : List (List (List ℕ))}
    (h : Rel m R1 R2) (g : Gate) :
    Rel m (R1 ++ [match g.op with
        | GateOp.or => (g.inputs.map fun i => R1.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => (g.inputs.map fun i => R1.getD i []).foldl (andStep 1) [S.map fun _ => 0]
        | _ => []])
      (R2 ++ [match g.op with
        | GateOp.or => (g.inputs.map fun i => R2.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => (g.inputs.map fun i => R2.getD i []).foldl (andStep 2) [S.map fun _ => 0]
        | _ => []]) := by
  have hnew : Inv m (match g.op with
        | GateOp.or => (g.inputs.map fun i => R1.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => (g.inputs.map fun i => R1.getD i []).foldl (andStep 1) [S.map fun _ => 0]
        | _ => [])
      (match g.op with
        | GateOp.or => (g.inputs.map fun i => R2.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => (g.inputs.map fun i => R2.getD i []).foldl (andStep 2) [S.map fun _ => 0]
        | _ => []) := by
    have hz : Inv m [S.map fun _ => 0] [S.map fun _ => 0] := by
      refine ⟨?_, ?_, ?_⟩ <;> intro u hu <;> simp at hu <;> subst hu <;> simp [hS]
    cases hop : g.op with
    | or => exact inv_orFold _ _ (rel_ins h _) _ _ (inv_nil m)
    | and => exact inv_andFold _ _ (rel_ins h _) _ _ hz
    | _ => exact inv_nil m
  refine ⟨by simp [h.1], fun i => ?_⟩
  rw [getD_append_single, getD_append_single, ← h.1]
  split_ifs
  · exact h.2 i
  · exact hnew
  · exact inv_nil m

theorem rel_fold {m : ℕ} (S : List ℕ) (hS : S.length = m) :
    ∀ (gs : List Gate) (R1 R2 : List (List (List ℕ))), Rel m R1 R2 →
    Rel m (gs.foldl (fun R g =>
        let ins := g.inputs.map fun i => R.getD i []
        R ++ [match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep 1) [S.map fun _ => 0]
          | _ => []]) R1)
      (gs.foldl (fun R g =>
        let ins := g.inputs.map fun i => R.getD i []
        R ++ [match g.op with
          | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
          | GateOp.and => ins.foldl (andStep 2) [S.map fun _ => 0]
          | _ => []]) R2) := by
  intro gs
  induction gs with
  | nil => intro R1 R2 h; exact h
  | cons g gs ih => intro R1 R2 h; simp only [List.foldl_cons]; exact ih _ _ (rel_step S hS h g)

theorem rel_leaves (S : List ℕ) (n : ℕ) :
    Rel S.length ((List.range n).map (leafVectors S 1)) ((List.range n).map (leafVectors S 2)) := by
  have he : ∀ i, leafVectors S 1 i = leafVectors S 2 i := by intro i; simp [leafVectors]
  refine ⟨by simp, fun i => ?_⟩
  have : ((List.range n).map (leafVectors S 1)) = ((List.range n).map (leafVectors S 2)) :=
    List.map_congr_left (fun i _ => he i)
  rw [this]
  refine ⟨?_, ?_, fun u hu _ => hu⟩ <;>
  · intro u hu
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hi)] at hu
      simp [leafVectors] at hu
      rw [hu.2]; simp
    · rw [List.getD_eq_default _ _ (by simpa using hi)] at hu; simp at hu

theorem readsAtMost_two_of_one (C : Circuit) (n : ℕ) (S : List ℕ)
    (h : readsAtMost C n S 1 = true) : readsAtMost C n S 2 = true := by
  unfold readsAtMost at h ⊢
  have hrel : Rel S.length (readVectors C n S 1) (readVectors C n S 2) :=
    rel_fold S rfl C.gates _ _ (rel_leaves S n)
  obtain ⟨v, hv, hall⟩ := List.any_eq_true.mp h
  have hg : Good v := fun a ha => by simpa using (List.all_eq_true.mp hall) a ha
  have hv2 := (hrel.2 C.output).2.2 v hv hg
  exact List.any_eq_true.mpr ⟨v, hv2, List.all_eq_true.mpr fun a ha => by
    have := hg a ha; simp; omega⟩

theorem isReadK_two_of_one {n : ℕ} {C : Circuit} (h : IsReadK n C 1) : IsReadK n C 2 :=
  fun S hS => readsAtMost_two_of_one C n _ (h S hS)

end Scratch.ReadMono

namespace Scratch.Forest2584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]

/-- The incidence graph of `I` on `Fin (P + L)`: points first, then lines. -/
def incGraph : SimpleGraph (Fin (P + L)) :=
  SimpleGraph.fromRel fun u v => ∃ p l, I p l ∧ u = Fin.castAdd L p ∧ v = Fin.natAdd P l

theorem castAdd_ne_natAdd (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem incGraph_adj_iff (u v : Fin (P + L)) : (incGraph I).Adj u v ↔
    ∃ p l, I p l ∧ ((u = Fin.castAdd L p ∧ v = Fin.natAdd P l) ∨
      (v = Fin.castAdd L p ∧ u = Fin.natAdd P l)) := by
  unfold incGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨p, l, h, rfl, rfl⟩ | ⟨p, l, h, rfl, rfl⟩⟩
    · exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨castAdd_ne_natAdd p l, Or.inl ⟨p, l, h, rfl, rfl⟩⟩
    · exact ⟨(castAdd_ne_natAdd p l).symm, Or.inr ⟨p, l, h, rfl, rfl⟩⟩

theorem exists_iff_adj (x : Fin (P + L) → Bool) :
    (∃ p : Fin P, ∃ l : Fin L, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) ↔
    ∃ a b : Fin (P + L), (incGraph I).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨p, l, h, h1, h2⟩
    exact ⟨_, _, (incGraph_adj_iff I _ _).mpr ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩, h1, h2⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (incGraph_adj_iff I a b).mp hab
    · exact ⟨p, l, h, ha, hb⟩
    · exact ⟨p, l, h, hb, ha⟩

/-- The incidences as a finset of pairs. -/
def incPairs : Finset (Fin P × Fin L) := Finset.univ.filter fun e => I e.1 e.2

theorem edgeSet_eq_image :
    (incGraph I).edgeSet = (fun e : Fin P × Fin L => s(Fin.castAdd L e.1, Fin.natAdd P e.2)) ''
      ((incPairs I : Finset (Fin P × Fin L)) : Set (Fin P × Fin L)) := by
  ext z
  induction z using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, incGraph_adj_iff]
    simp only [incPairs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨p, l, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨p, l, h, rfl⟩
      · exact ⟨p, l, h, Sym2.eq_swap⟩
    · rintro ⟨p, l, h, he⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨p, l, h, Or.inl ⟨h1.symm, h2.symm⟩⟩
      · exact ⟨p, l, h, Or.inr ⟨h1.symm, h2.symm⟩⟩

theorem edge_ncard : (incGraph I).edgeSet.ncard = (incPairs I).card := by
  rw [edgeSet_eq_image, Set.ncard_image_of_injective _ ?_, Set.ncard_coe_finset]
  rintro ⟨p, l⟩ ⟨p', l'⟩ he
  simp only at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : p = p' := Fin.ext (by simpa using congrArg Fin.val h1)
    have e2 : l = l' := Fin.ext (by simpa using congrArg Fin.val h2)
    rw [e1, e2]
  · exact absurd h1 (castAdd_ne_natAdd p l')

theorem card_split (T : Finset (Fin (P + L))) :
    (Finset.univ.filter fun p : Fin P => Fin.castAdd L p ∈ T).card +
      (Finset.univ.filter fun l : Fin L => Fin.natAdd P l ∈ T).card = T.card := by
  have hA : (Finset.univ.filter fun p : Fin P => Fin.castAdd L p ∈ T).map (Fin.castAddEmb L) =
      T.filter fun v => v.val < P := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castAddEmb_apply]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨hp, by simp⟩
    · rintro ⟨hv, hlt⟩
      have hc : Fin.castAdd L (⟨v.val, hlt⟩ : Fin P) = v := Fin.ext (by simp)
      exact ⟨⟨v.val, hlt⟩, by rw [hc]; exact hv, hc⟩
  have hB : (Finset.univ.filter fun l : Fin L => Fin.natAdd P l ∈ T).map (Fin.natAddEmb P) =
      T.filter fun v => ¬ v.val < P := by
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.natAddEmb_apply]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨hl, by simp⟩
    · rintro ⟨hv, hlt⟩
      refine ⟨⟨v.val - P, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
      convert hv using 1; exact Fin.ext (by simp; omega)
  have e1 := Finset.card_map (s := Finset.univ.filter fun p : Fin P => Fin.castAdd L p ∈ T)
    (Fin.castAddEmb L)
  have e2 := Finset.card_map (s := Finset.univ.filter fun l : Fin L => Fin.natAdd P l ∈ T)
    (Fin.natAddEmb P)
  rw [hA] at e1; rw [hB] at e2
  have e3 := Finset.card_filter_add_card_filter_not (s := T) (fun v : Fin (P + L) => v.val < P)
  omega

theorem monotone2_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    Monotone2 C := by
  intro g hg
  obtain ⟨hao, -, hlen⟩ := h
  refine ⟨?_, by rw [hlen g hg]⟩
  rcases hao g hg with h1 | h1 <;> simp [h1]

/-- L-meta-2584 restricted to forests: when the incidence graph has no cycle, every AO2 circuit
for the incidence function has a no-larger AO2 circuit for it that is read-1, hence read-2. -/
theorem forest_case (C : Circuit) (hac : (incGraph I).IsAcyclic)
    (hC : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L,
      I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L,
        I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  classical
  -- a least vertex cover
  obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset (Fin (P + L)))).filter
      fun S => CoverPromise.IsVertexCover (incGraph I) S) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
  have hTcov : CoverPromise.IsVertexCover (incGraph I) T := (Finset.mem_filter.mp hTmem).2
  have hmin : ∀ S : Finset (Fin (P + L)), CoverPromise.IsVertexCover (incGraph I) S →
      T.card ≤ S.card := fun S hS => hTmin S (by simp [hS])
  -- the lower bound for forests
  have hev : ∀ x : Fin (P + L) → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin (P + L), (incGraph I).Adj a b ∧ x a = true ∧ x b = true := by
    intro x
    have := hF x
    simp only [circuitFun] at this
    rw [this, decide_eq_true_iff, exists_iff_adj]
  have hlow := PEqualNP.Outside.L_meta_3525 (P + L) T.card (incGraph I) C hac hmin
    (monotone2_of_isAO2 hC) hev
  -- the star cover of the incidences on the two halves of `T`
  obtain ⟨D, hD, hDs, hDf, hDr⟩ := PEqualNP.Outside.L_meta_7684 P L (incPairs I)
    (Finset.univ.filter fun p : Fin P => Fin.castAdd L p ∈ T)
    (Finset.univ.filter fun l : Fin L => Fin.natAdd P l ∈ T) (by
      intro e he
      have hI : I e.1 e.2 := (Finset.mem_filter.mp he).2
      rcases hTcov _ _ ((incGraph_adj_iff I _ _).mpr ⟨e.1, e.2, hI, Or.inl ⟨rfl, rfl⟩⟩) with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h]))
  refine ⟨D, hD, ?_, ?_, Scratch.ReadMono.isReadK_two_of_one hDr⟩
  · intro y
    rw [hDf y]
    simp [incPairs]
  · have hsplit := card_split T
    rw [edge_ncard] at hlow
    omega

end Scratch.Forest2584
