/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma sum_ee : ∑ x : ZMod 17, ee x = 0 := by
  have h : ∑ x : ZMod 17, ee x = ∑ n ∈ Finset.range 17, zeta ^ n := by
    rw [Finset.sum_nbij' (i := fun (x : ZMod 17) => x.val) (j := fun (n : ℕ) => (n : ZMod 17))] <;>
      simp [ZMod.val_lt, ee]
  rw [h, geom_sum_eq zeta_ne_one, zeta_pow_17]
  simp

