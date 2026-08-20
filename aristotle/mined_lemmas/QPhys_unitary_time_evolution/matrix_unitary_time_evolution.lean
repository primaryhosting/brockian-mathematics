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

