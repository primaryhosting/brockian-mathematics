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

private theorem sum_expand (ψ ϕ : Fin d → ℂ) :
    ∑ i, ∑ j, (ψ i * ϕ j + ψ j * ϕ i) *
        (conj (ψ i) * conj (ϕ j) + conj (ψ j) * conj (ϕ i))
      = 2 * ((∑ i, ψ i * conj (ψ i)) * (∑ j, ϕ j * conj (ϕ j)))
        + 2 * ((∑ i, ψ i * conj (ϕ i)) * (∑ j, ϕ j * conj (ψ j))) := by
  have h1 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f i * g j = (∑ i, f i) * (∑ j, g j) := by
    intro f g; rw [Finset.sum_mul_sum]
  have h2 : ∀ f g : Fin d → ℂ, ∑ i, ∑ j, f j * g i = (∑ j, f j) * (∑ i, g i) := by
    intro f g; rw [Finset.sum_comm, Finset.sum_mul_sum]
  have e : ∀ i j : Fin d,
      (ψ i * ϕ j + ψ j * ϕ i) * (conj (ψ i) * conj (ϕ j) + conj (ψ j) * conj (ϕ i))
        = (ψ i * conj (ψ i)) * (ϕ j * conj (ϕ j)) + (ψ i * conj (ϕ i)) * (ϕ j * conj (ψ j))
          + (ψ j * conj (ψ j)) * (ϕ i * conj (ϕ i))
          + (ψ j * conj (ϕ j)) * (ϕ i * conj (ψ i)) := by
    intro i j; ring
  simp only [e, Finset.sum_add_distrib, h1, h2]
  ring

/-- A unit vector of `EuclideanSpace ℂ (Fin d)` has `∑ i, ψ i * conj (ψ i) = 1`. -/
