import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

theorem artinPrimeSet_neg_one : artinPrimeSet (-1) = {2, 3} := by
  ext p
  simp only [artinPrimeSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hroot⟩
    have hle : p ≤ 3 := by
      by_contra hlt
      exact not_isPrimitiveRootMod_of_exceptional (-1) p hp (by omega) (Or.inl rfl) hroot
    have h2 := hp.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, isPrimitiveRootMod_neg_one_two⟩
    · exact ⟨by norm_num, isPrimitiveRootMod_neg_one_three⟩

end Frontier

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

