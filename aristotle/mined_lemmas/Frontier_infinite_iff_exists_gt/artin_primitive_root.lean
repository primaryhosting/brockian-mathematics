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

/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/

theorem artin_primitive_root :
    (ArtinConjecture ↔ ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ,
        ∃ p : ℕ, N < p ∧ p.Prime ∧ IsPrimitiveRootMod a p) ∧
    (∀ a : ℤ, IsSquare a → ∀ p ∈ artinSet a, p = 2) ∧
    (∀ p ∈ artinSet (-1 : ℤ), p ≤ 3) ∧
    (∀ (a : ℤ) (p : ℕ), p.Prime → (a : ZMod p) ≠ 0 →
        (p ∈ artinSet a ↔ ∀ q : ℕ, q.Prime → q ∣ (p - 1) →
          ((a : ZMod p)) ^ ((p - 1) / q) ≠ 1)) ∧
    ({3, 5, 11, 13} : Set ℕ) ⊆ artinSet 2 := by
  refine ⟨artinConjecture_iff, fun a ha p hp => square_not_primitiveRoot ha hp,
    fun p hp => neg_one_not_primitiveRoot hp, ?_, ?_⟩
  · intro a p hp ha
    have : (p ∈ artinSet a) ↔ (p.Prime ∧ IsPrimitiveRootMod a p) := Iff.rfl
    rw [this, isPrimitiveRootMod_iff hp ha]
    exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
  · intro p hp
    rcases hp with h | h | h | h <;> subst h
    · exact ⟨by norm_num, two_primitiveRoot_three⟩
    · exact ⟨by norm_num, two_primitiveRoot_five⟩
    · exact ⟨by norm_num, two_primitiveRoot_eleven⟩
    · exact ⟨by norm_num, two_primitiveRoot_thirteen⟩

end Frontier

