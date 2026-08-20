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

theorem star_neg_I_smul_eq_neg {H : A} (hH : IsSelfAdjoint H) (s : ℝ) :
    star ((-(Complex.I * (s : ℝ))) • H) = -((-(Complex.I * (s : ℝ))) • H) := by
  rw [star_smul, hH.star_eq, ← neg_smul]
  congr 1
  simp

/-- **Unitary time evolution.** For a self-adjoint Hamiltonian `H` in a Banach `*`-algebra over
`ℂ` (e.g. a C*-algebra of bounded operators, or complex matrices), the time evolution operator
`U(t) = exp (-i H t / ℏ)` is unitary for every real time `t`: it satisfies
`U(t)* U(t) = 1 = U(t) U(t)*`. -/
