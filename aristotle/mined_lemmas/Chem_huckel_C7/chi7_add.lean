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

lemma chi7_add (a b : ZMod 7) : chi7 (a + b) = chi7 a * chi7 b := by
  have hab : a + b = ((a.val + b.val : ℕ) : ZMod 7) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  rw [hab, ← zeta7_pow_natCast, pow_add, chi7, chi7]

