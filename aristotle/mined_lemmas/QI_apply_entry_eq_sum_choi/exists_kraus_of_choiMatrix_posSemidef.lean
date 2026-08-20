import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open Matrix

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

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The amplification `id_p ⊗ Φ` of a linear map `Φ` between matrix algebras:
a `(p × n)`-matrix is viewed as a `p × p` block matrix of `n × n` blocks, and `Φ`
is applied to each block. -/

lemma exists_kraus_of_choiMatrix_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ V : (n × m) → Matrix m n ℂ, ∀ X : Matrix n n ℂ, Φ X = ∑ s, V s * X * (V s)ᴴ := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (n × m) (n × m) ℂ, choiMatrix Φ = Bᴴ * B :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr h)
  refine ⟨fun s => Matrix.of fun k i => star (B s (i, k)), fun X => ?_⟩
  ext k l
  rw [apply_entry_eq_sum_choi Φ X k l, hB]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_star, Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ i : n, ∑ j : n, ∑ s : n × m, X i j * (star (B s (i, k)) * B s (j, l))
      = ∑ s : n × m, ∑ j : n, X i j * (star (B s (i, k)) * B s (j, l)) :=
    fun i => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

omit [Fintype m] [DecidableEq m] in
/-- The Choi matrix is the image, under the amplification `id_n ⊗ Φ`, of the (unnormalized)
maximally entangled state. -/
