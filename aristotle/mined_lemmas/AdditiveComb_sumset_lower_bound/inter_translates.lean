/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset Pointwise

/-- The two translated copies `A + max B` and `min A + B` both sit inside `A + B`. -/

private lemma inter_translates {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.max' hB)) ∩ (B.image (fun b => A.min' hA + b))
      = {A.min' hA + B.max' hB} := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_inter.1 hx with ⟨h1, h2⟩
    rcases Finset.mem_image.1 h1 with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.1 h2 with ⟨b, hb, hab⟩
    have ha' : A.min' hA ≤ a := A.min'_le a ha
    have hb' : b ≤ B.max' hB := B.le_max' b hb
    have : a = A.min' hA := by omega
    simp [this]
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_inter.2
      ⟨Finset.mem_image.2 ⟨A.min' hA, A.min'_mem hA, rfl⟩,
       Finset.mem_image.2 ⟨B.max' hB, B.max'_mem hB, rfl⟩⟩

/-- **Sumset lower bound over the integers** (the Cauchy–Davenport analogue / base case of
Freiman's lemma): for finite nonempty sets `A`, `B` of integers,
`|A| + |B| - 1 ≤ |A + B|`. -/
