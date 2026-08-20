import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

theorem artin_primitive_root :
    (∀ a : ℤ, IsSquare a → (artinPrimes a).Finite) ∧
    (artinPrimes (-1)).Finite ∧
    {p : ℕ | p.Prime ∧ ∃ a : ℤ, IsPrimitiveRootMod a p}.Infinite ∧
    ({3, 5, 11, 13} : Set ℕ) ⊆ artinPrimes 2 ∧
    (ArtinConjecture ↔ ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧
      p.Prime ∧ IsPrimitiveRootMod a p) := by
  refine ⟨fun a ha => finite_artinPrimes_of_isSquare ha, finite_artinPrimes_neg_one,
    infinite_primes_with_primitive_root, ?_, artinConjecture_iff⟩
  rintro p (rfl | rfl | rfl | rfl)
  · exact ⟨by norm_num, two_primitive_root_three⟩
  · exact ⟨by norm_num, two_primitive_root_five⟩
  · exact ⟨by norm_num, two_primitive_root_eleven⟩
  · exact ⟨by norm_num, two_primitive_root_thirteen⟩

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

