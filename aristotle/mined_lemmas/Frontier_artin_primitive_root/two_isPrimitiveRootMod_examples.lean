/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` has
multiplicative order exactly `p - 1`, i.e. it generates the group `(ZMod p)ˣ`. -/

theorem two_isPrimitiveRootMod_examples :
    IsPrimitiveRootMod 2 3 ∧ IsPrimitiveRootMod 2 5 ∧ IsPrimitiveRootMod 2 11 ∧
      IsPrimitiveRootMod 2 13 ∧ IsPrimitiveRootMod 2 19 ∧ IsPrimitiveRootMod 2 29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · show orderOf _ = _
      norm_num
      rw [orderOf_eq_iff (by norm_num)]
      exact ⟨by decide, by decide⟩

/-- Artin's conjecture is equivalent to: for each admissible `a` the primes having `a`
as a primitive root are unbounded. -/
