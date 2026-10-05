/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

theorem PentagonIsotypicDecomposition :
    isoPlane 5 0 ⊔ isoPlane 5 1 ⊔ isoPlane 5 2 = ⊤
    ∧ Module.finrank ℂ (isoPlane 5 0) = 1
    ∧ Module.finrank ℂ (isoPlane 5 1) = 2
    ∧ Module.finrank ℂ (isoPlane 5 2) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← iSup_isoPlane 5, iSup_le_iff]
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = -(2 : ZMod 5) ∨ k = -(1 : ZMod 5) := by
      revert k; decide
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
    · rw [isoPlane_neg]; exact le_sup_right
    · rw [isoPlane_neg]; exact le_sup_of_le_left le_sup_right
  · exact finrank_isoPlane_of_eq 5 0 (by decide)
  · exact finrank_isoPlane_of_ne 5 1 (by decide)
  · exact finrank_isoPlane_of_ne 5 2 (by decide)

end

end Brockian

import Mathlib

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

