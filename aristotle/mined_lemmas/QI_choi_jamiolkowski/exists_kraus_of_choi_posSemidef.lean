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

lemma exists_kraus_of_choi_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choi Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ X : Matrix n n ℂ, Φ X = ∑ c, V c * X * (V c)ᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  refine ⟨fun c => Matrix.of fun i a => star (B c (a, i)), fun X => ?_⟩
  ext i j
  rw [apply_apply_eq_sum_choi]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, hB, Matrix.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm_three (fun a b c => X a b * (star (B c (a, i)) * B c (b, j)))]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => by ring

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus decomposition `X ↦ ∑ c, V c * X * (V c)ᴴ` is completely positive. -/
