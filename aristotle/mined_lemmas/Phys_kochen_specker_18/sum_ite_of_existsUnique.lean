/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

private lemma sum_ite_of_existsUnique {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : ∃! i, P i) : ∑ i, (if P i then (1 : ℕ) else 0) = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have hcongr : ∀ j : Fin n, (if P j then (1 : ℕ) else 0) = if j = i then 1 else 0 := by
    intro j
    by_cases hj : P j
    · rw [if_pos hj, if_pos (hu j hj)]
    · have : j ≠ i := by rintro rfl; exact hj hi
      simp [hj, this]
  simp [Finset.sum_congr rfl (fun j _ => hcongr j)]

/-- **Kochen–Specker (18 vectors).**  The explicit 18-vector configuration in `ℝ⁴` of
Cabello, Estebaranz and García-Alcaine consists of 18 distinct nonzero vectors arranged into
9 orthogonal bases (four pairwise orthogonal vectors each), and admits no `{0,1}`-coloring:
there is no assignment of a truth value to each vector such that in every one of the nine
bases exactly one vector is assigned `true`. -/
