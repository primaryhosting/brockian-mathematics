import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

open MeasureTheory

noncomputable section

namespace QI

/-! ## The quantum ingredients

We work with a single qubit modelled as `Fin 2 → ℂ` and a pair of qubits modelled as
`Fin 2 × Fin 2 → ℂ` (the tensor product `ℂ² ⊗ ℂ²`), equipped with the standard Hermitian
inner product `inner2`.
-/

/-- The scalar `1/√2`. -/

lemma invSqrtTwo_mul : invSqrtTwo * invSqrtTwo = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  unfold invSqrtTwo
  field_simp
  linear_combination -h2

