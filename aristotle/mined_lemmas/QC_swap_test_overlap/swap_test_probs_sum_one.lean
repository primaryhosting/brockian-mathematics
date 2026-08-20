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

theorem swap_test_probs_sum_one (ψ ϕ : EuclideanSpace ℂ (Fin d))
    (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    swapTestAcceptProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ)
      + swapTestRejectProb (WithLp.ofLp ψ) (WithLp.ofLp ϕ) = 1 := by
  rw [swap_test_overlap ψ ϕ hψ hϕ, swap_test_reject ψ ϕ hψ hϕ]
  ring

end QC

