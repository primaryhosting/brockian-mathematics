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

theorem timeEvolution_isUnit (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    IsUnit (timeEvolution hbar H t) :=
  ⟨⟨timeEvolution hbar H t, star (timeEvolution hbar H t),
    (unitary_time_evolution hbar hH t).2.2, (unitary_time_evolution hbar hH t).2.1⟩, rfl⟩

end BanachStarAlgebra

section Matrices

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix form of unitary time evolution: for a Hermitian matrix `H`, the matrix
`U(t) = exp (-i H t / ℏ)` satisfies `Uᴴ * U = 1` and `U * Uᴴ = 1`. -/
