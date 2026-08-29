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

lemma zeta7_pow_natCast (n : ℕ) : zeta7 ^ n = chi7 (n : ZMod 7) := by
  have h : (n : ZMod 7).val = n % 7 := by simp [ZMod.val_natCast]
  rw [chi7, h]
  conv_lhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, zeta7_pow_seven, one_pow, one_mul]

