/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Statement: CP maps correspond to positive Choi matrices (Choi–Jamiołkowski isomorphism).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n m : ℕ}

/-- A linear map between spaces of square complex matrices. -/
abbrev MatMap (n m : ℕ) := Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ

/-- The Choi matrix of a linear map `Φ`:
`C_{(a,s),(b,t)} = Φ(E_{ab})_{s,t}`, i.e. `C = ∑_{a,b} E_{ab} ⊗ Φ(E_{ab})`. -/

lemma apply_eq_sum_choiMatrix (Φ : MatMap n m) (A : Matrix (Fin n) (Fin n) ℂ) (s t : Fin m) :
    Φ A s t = ∑ a, ∑ b, A a b * choiMatrix Φ (a, s) (b, t) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply, choiMatrix, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : Matrix.single a b (A a b) = A a b • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.smul_single]; simp
  rw [h, map_smul]
  simp

/-- If `Φ` has a Kraus representation, its amplifications are conjugations by `id_k ⊗ V r`. -/
