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

lemma chi7_add_chi7_neg (k : ZMod 7) : chi7 k + chi7 (-k) = lam7 k := by
  rw [chi7_eq_exp, chi7_neg_eq_exp, lam7]
  have h := Complex.two_cos ((2 * Real.pi * k.val / 7 : ℝ) : ℂ)
  push_cast at h ⊢
  rw [← neg_mul]
  linear_combination -h

/-- The action of the adjacency matrix on a vector. -/
