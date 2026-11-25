import Mathlib
import PEqualNP.Defs

namespace Scratch.Equiv2584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]

/-- `C` computes the incidence function of `I`. -/
def Computes (C : Circuit) : Prop :=
  ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
    decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)

/-- The per-graph form of L-meta-2584: every AO2 circuit for the incidence function has a no-larger
read-2 AO2 circuit for it. -/
def Replaceable : Prop :=
  ∀ C : Circuit, PEqualNP.TopForm.IsAO2 (P + L) C → Computes P L I C →
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ Computes P L I D ∧ D.size ≤ C.size ∧
      PEqualNP.ReadK.IsReadK (P + L) D 2

/-- Some least AO2 circuit for the incidence function is read-2 (whenever one circuit exists). -/
def LeastReadTwo : Prop :=
  (∃ C : Circuit, PEqualNP.TopForm.IsAO2 (P + L) C ∧ Computes P L I C) →
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ Computes P L I D ∧
      PEqualNP.ReadK.IsReadK (P + L) D 2 ∧
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 (P + L) C → Computes P L I C → D.size ≤ C.size

theorem replaceable_iff_leastReadTwo : Replaceable P L I ↔ LeastReadTwo P L I := by
  classical
  constructor
  · intro h ⟨C, hC, hF⟩
    -- the least size of an AO2 circuit for the function
    have hex : ∃ k, ∃ C : Circuit, PEqualNP.TopForm.IsAO2 (P + L) C ∧ Computes P L I C ∧ C.size = k :=
      ⟨C.size, C, hC, hF, rfl⟩
    obtain ⟨C0, hC0, hF0, hs0⟩ := Nat.find_spec hex
    obtain ⟨D, hD, hFD, hDs, hR⟩ := h C0 hC0 hF0
    refine ⟨D, hD, hFD, hR, fun C' hC' hF' => ?_⟩
    have : Nat.find hex ≤ C'.size := Nat.find_min' hex ⟨C', hC', hF', rfl⟩
    omega
  · intro h C hC hF
    obtain ⟨D, hD, hFD, hR, hmin⟩ := h ⟨C, hC, hF⟩
    exact ⟨D, hD, hFD, hmin C hC hF, hR⟩

end Scratch.Equiv2584
