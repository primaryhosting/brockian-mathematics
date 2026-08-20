import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
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

namespace Math2

open Matrix

variable {n : ℕ}

/-- The standard symplectic form on `ℝ ^ (2 * n)`, with `ℝ ^ (2 * n)` modelled as functions
`(Fin n ⊕ Fin n) → ℝ`: the coordinates indexed by `Sum.inl i` are the positions `qᵢ` and the
coordinates indexed by `Sum.inr i` are the momenta `pᵢ`. -/

def cylinder (i₀ : Fin n) (R : ℝ) : Set ((Fin n ⊕ Fin n) → ℝ) :=
  {y | y (Sum.inl i₀) ^ 2 + y (Sum.inr i₀) ^ 2 ≤ R ^ 2}

/-- The symplectic form written through the matrix `J`. -/
