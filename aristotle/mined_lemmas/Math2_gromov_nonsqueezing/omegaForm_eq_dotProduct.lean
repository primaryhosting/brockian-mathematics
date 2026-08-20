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

lemma omegaForm_eq_dotProduct (x y : (Fin n ⊕ Fin n) → ℝ) :
    omegaForm x y = -(x ⬝ᵥ (Matrix.J (Fin n) ℝ *ᵥ y)) := by
  simp [omegaForm, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.one_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- Matrices in the symplectic group act on `ℝ ^ (2 * n)` by symplectic linear maps: they preserve
the standard symplectic form `omegaForm`. -/
