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
noncomputable def timeEvolution (hbar : ℝ) (H : A) (t : ℝ) : A :=
  exp ((-(Complex.I * (t / hbar : ℝ))) • H)

omit [StarModule ℂ A] in
/-- **Key intermediate lemma.** In a Banach `*`-algebra, the exponential of a skew-adjoint
element is unitary: if `star x = -x`, then `exp x` is unitary, because
`star (exp x) = exp (star x) = exp (-x)` is a two-sided inverse of `exp x`. -/
theorem exp_mem_unitary_of_star_eq_neg {x : A} (hx : star x = -x) : exp x ∈ unitary A := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  constructor
  · rw [star_exp, hx, ← exp_add_of_commute (Commute.neg_left (Commute.refl x)),
      neg_add_cancel, exp_zero]
  · rw [star_exp, hx, ← exp_add_of_commute (Commute.neg_right (Commute.refl x)),
      add_neg_cancel, exp_zero]

omit [ContinuousStar A] [CompleteSpace A] in
/-- For a self-adjoint `H` and a real scalar `s`, the element `-i s H` is skew-adjoint. -/
theorem star_neg_I_smul_eq_neg {H : A} (hH : IsSelfAdjoint H) (s : ℝ) :
    star ((-(Complex.I * (s : ℝ))) • H) = -((-(Complex.I * (s : ℝ))) • H) := by
  rw [star_smul, hH.star_eq, ← neg_smul]
  congr 1
  simp

/-- **Unitary time evolution.** For a self-adjoint Hamiltonian `H` in a Banach `*`-algebra over
`ℂ` (e.g. a C*-algebra of bounded operators, or complex matrices), the time evolution operator
`U(t) = exp (-i H t / ℏ)` is unitary for every real time `t`: it satisfies
`U(t)* U(t) = 1 = U(t) U(t)*`. -/
theorem unitary_time_evolution (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    timeEvolution hbar H t ∈ unitary A ∧
      star (timeEvolution hbar H t) * timeEvolution hbar H t = 1 ∧
      timeEvolution hbar H t * star (timeEvolution hbar H t) = 1 := by
  have h : timeEvolution hbar H t ∈ unitary A :=
    exp_mem_unitary_of_star_eq_neg (star_neg_I_smul_eq_neg hH (t / hbar))
  exact ⟨h, h.1, h.2⟩

/-- The time evolution operator is invertible, with inverse `U(-t)`-like adjoint `U(t)*`. -/
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
theorem matrix_unitary_time_evolution (hbar : ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian) (t : ℝ) :
    letI U : Matrix n n ℂ := exp ((-(Complex.I * (t / hbar : ℝ))) • H)
    Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hsa : IsSelfAdjoint H := hH
  have h := unitary_time_evolution (A := Matrix n n ℂ) hbar hsa t
  exact ⟨h.2.1, h.2.2⟩

end Matrices

end QPhys

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

