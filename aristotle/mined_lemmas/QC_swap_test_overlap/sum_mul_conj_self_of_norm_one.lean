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

private theorem sum_mul_conj_self_of_norm_one (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    ∑ i, ψ i * conj (ψ i) = (1 : ℂ) := by
  have hsum : ∑ i, ‖ψ i‖ ^ 2 = (1 : ℝ) := by
    have h := EuclideanSpace.norm_eq ψ
    rw [hψ] at h
    have h' := congrArg (fun t => t ^ 2) h
    simp only at h'
    rw [Real.sq_sqrt (by positivity)] at h'
    linarith [h']
  calc ∑ i, ψ i * conj (ψ i) = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun i _ => (ofReal_norm_sq (ψ i)).symm
    _ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [hsum]; norm_num

/-- **The SWAP test.**  For unit vectors `ψ` and `ϕ`, the SWAP test on
`|0⟩|ψ⟩|ϕ⟩` accepts (measures `0` on the ancilla) with probability
`(1 + |⟨ψ|ϕ⟩|²)/2`. -/
