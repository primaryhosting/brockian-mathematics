import Mathlib

/-!
# Unitary Time Evolution
Category: Quantum Physics
Target: QPhys.unitary_time_evolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

section BanachStarAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The time evolution operator `U(t) = exp (-i H t / ℏ)` associated with a Hamiltonian `H`
(an element of a Banach `*`-algebra over `ℂ`), Planck's reduced constant `ℏ`, and a time `t`. -/

theorem exp_mem_unitary_of_star_eq_neg {x : A} (hx : star x = -x) : exp x ∈ unitary A := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  constructor
  · rw [star_exp, hx, ← exp_add_of_commute (Commute.neg_left (Commute.refl x)),
      neg_add_cancel, exp_zero]
  · rw [star_exp, hx, ← exp_add_of_commute (Commute.neg_right (Commute.refl x)),
      add_neg_cancel, exp_zero]

omit [ContinuousStar A] [CompleteSpace A] in
/-- For a self-adjoint `H` and a real scalar `s`, the element `-i s H` is skew-adjoint. -/
