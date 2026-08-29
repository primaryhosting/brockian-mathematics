/-
# Landau Levels — a concrete model
A Fock-space realization of the ladder-operator hypotheses used in
`Frontier.landau_levels`, showing that they are consistent and that every
level `ℏ ω_c (n + 1/2)` really occurs.
-/

import Mathlib
import RequestProject.LandauLevels

namespace Frontier.Fock

/-! ### The inner product on finitely supported sequences -/

/-- The Fock inner product on finitely supported complex sequences. -/

theorem landau_hypotheses_consistent :
    (∀ x y : ℕ →₀ ℂ, (inner ℂ (aOp x) y : ℂ) = (inner ℂ x (adagOp y) : ℂ)) ∧
      (∀ x : ℕ →₀ ℂ, aOp (adagOp x) - adagOp (aOp x) = x) :=
  ⟨fun x y => by rw [inner_eq_finner, inner_eq_finner]; exact fock_adjoint x y, fock_ccr⟩

end Frontier.Fock

/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Frontier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- If `B` acts as the adjoint of `A` and `v` is an eigenvector of the number operator
`N = B ∘ A` with eigenvalue `μ`, then `μ` is a nonnegative real number
(indeed `μ = ‖A v‖² / ‖v‖²`). -/
