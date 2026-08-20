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

set_option grind.warning false

open scoped ComplexConjugate

namespace QC

variable {d : ℕ}

/-- Index type for the three registers used in the SWAP test: a one-qubit
ancilla (`Fin 2`) together with two `d`-dimensional data registers.  A state of
the whole system is a complex amplitude function on this index type. -/
abbrev Reg (d : ℕ) : Type := Fin 2 × Fin d × Fin d

/-- The initial state of the SWAP test, `|0⟩ ⊗ |ψ⟩ ⊗ |ϕ⟩`. -/

theorem swapTestState_one (ψ ϕ : Fin d → ℂ) (i j : Fin d) :
    swapTestState ψ ϕ (1, i, j) = (2 : ℂ)⁻¹ * (ψ i * ϕ j - ψ j * ϕ i) := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [swapTestState, hadamardAncilla, cswap, initState]
  norm_num
  linear_combination (ψ i * ϕ j - ψ j * ϕ i) * h2

/-- Casting the squared norm of a complex number: `‖z‖² = z * conj z`. -/
