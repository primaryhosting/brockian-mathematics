/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/

lemma sum_chi7_mul (m : ZMod 7) :
    ∑ k : ZMod 7, chi7 (m * k) = if m = 0 then 7 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [chi7_zero]
  · rw [if_neg hm]
    have hbij : ∑ k : ZMod 7, chi7 (m * k) = ∑ k : ZMod 7, chi7 k :=
      Fintype.sum_bijective (fun k => m * k) (Equiv.mulLeft₀ m hm).bijective _ _ (fun _ => rfl)
    rw [hbij, sum_chi7]

/-- The `k`-th Fourier coefficient of a vector. -/
