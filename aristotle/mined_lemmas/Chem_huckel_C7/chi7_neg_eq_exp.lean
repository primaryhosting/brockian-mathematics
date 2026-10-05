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

lemma chi7_neg_eq_exp (k : ZMod 7) :
    chi7 (-k) = Complex.exp (-((2 * Real.pi * k.val / 7 : ℝ) * Complex.I)) := by
  have h := chi7_mul_neg k
  rw [chi7_eq_exp] at h
  rw [Complex.exp_neg]
  exact eq_inv_of_mul_eq_one_left (by linear_combination h)

