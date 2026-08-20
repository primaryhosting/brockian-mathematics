import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder
open scoped MatrixOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`:
the block matrix whose `(a, b)` block is `Φ (single a b 1)`, i.e.
`Choi Φ = (id ⊗ Φ) (|Ω⟩⟨Ω|)` for the unnormalised maximally entangled vector `Ω`. -/

lemma choi_eq_ampliation (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    choi Φ = ampliation Φ n (maxEntangled n) := by
  ext p q
  simp only [choi, ampliation, Matrix.of_apply]
  have key : (Matrix.of fun s t => maxEntangled n (p.1, s) (q.1, t))
      = Matrix.single p.1 q.1 (1 : ℂ) := by
    ext s t
    simp only [maxEntangled, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.replicateCol_apply, Matrix.of_apply, Matrix.single_apply]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    by_cases h1 : p.1 = s <;> by_cases h2 : q.1 = t <;> simp [h1, h2]
  rw [key]

/-- Choi's theorem: a positive semidefinite Choi matrix yields a Kraus decomposition. -/
