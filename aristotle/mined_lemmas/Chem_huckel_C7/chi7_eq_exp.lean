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

lemma chi7_eq_exp (k : ZMod 7) :
    chi7 k = Complex.exp ((2 * Real.pi * k.val / 7 : ℝ) * Complex.I) := by
  rw [chi7, zeta7, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

