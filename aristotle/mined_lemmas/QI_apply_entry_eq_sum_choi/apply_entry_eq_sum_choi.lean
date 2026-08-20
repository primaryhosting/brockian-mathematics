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

lemma apply_entry_eq_sum_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (X : Matrix n n ℂ) (k l : m) :
    Φ X k l = ∑ i : n, ∑ j : n, X i j * choiMatrix Φ (i, k) (j, l) := by
  have hsingle : ∀ i j : n, Φ (Matrix.single i j (X i j)) k l
      = X i j * choiMatrix Φ (i, k) (j, l) := by
    intro i j
    rw [show Matrix.single i j (X i j) = (X i j) • Matrix.single i j (1 : ℂ) by simp, map_smul]
    simp [choiMatrix, Matrix.of_apply, smul_eq_mul]
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, hsingle]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus representation is completely positive. -/
