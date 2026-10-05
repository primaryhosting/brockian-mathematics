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

private lemma union_translates_subset {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.max' hB)) ∪ (B.image (fun b => A.min' hA + b)) ⊆ A + B := by
  intro x hx
  rcases Finset.mem_union.1 hx with hx | hx
  · rcases Finset.mem_image.1 hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add ha (B.max'_mem hB)
  · rcases Finset.mem_image.1 hx with ⟨b, hb, rfl⟩
    exact Finset.add_mem_add (A.min'_mem hA) hb

/-- The two translated copies meet exactly in the single point `min A + max B`. -/
