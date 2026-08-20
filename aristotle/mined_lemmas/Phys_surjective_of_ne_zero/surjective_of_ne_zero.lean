/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace Phys

open Representation

variable {k G M N : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The range of an intertwining map, as a subrepresentation of the target. -/

theorem surjective_of_ne_zero {ρ : Representation k G M} {σ : Representation k G N}
    [σ.IsIrreducible] (C : M →ₗ[k] N) (hC : ∀ g x, C (ρ g x) = σ g (C x)) (hC0 : C ≠ 0) :
    Function.Surjective C := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (rangeSubrep C hC) with h | h
  · exact absurd (by
      ext x
      have : C x ∈ (rangeSubrep C hC : Subrepresentation σ) := ⟨x, rfl⟩
      rw [h] at this
      simpa using this) hC0
  · intro n
    have : n ∈ (rangeSubrep C hC : Subrepresentation σ) := by rw [h]; trivial
    exact this

/-- **Schur-type rigidity**: if `C` and `T` are intertwining maps from `ρ` to an irreducible,
finite-dimensional representation `σ` over an algebraically closed field, `C ≠ 0`, and every
vector killed by `C` is killed by `T` (the multiplicity-one condition), then `T` is a unique
scalar multiple of `C`. -/
