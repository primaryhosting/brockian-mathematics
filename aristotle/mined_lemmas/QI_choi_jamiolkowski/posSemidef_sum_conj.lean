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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {N M : ℕ}

/-- A linear map between matrix algebras `M_N(ℂ) → M_M(ℂ)`. -/
abbrev MatMap (N M : ℕ) : Type :=
  Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ

/-- The amplification `id_{M_k} ⊗ Φ`, acting on `k × k` block matrices with blocks in
`M_N(ℂ)` by applying `Φ` to each block. -/

lemma posSemidef_sum_conj (k : ℕ) (A : Matrix (Fin k × Fin N) (Fin k × Fin N) ℂ)
    (hA : A.PosSemidef) (s : Finset (Fin N × Fin M))
    (V : Fin N × Fin M → Matrix (Fin M) (Fin N) ℂ) :
    (∑ r ∈ s, krausAmpl k (V r) * A * (krausAmpl k (V r))ᴴ).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert r s hr ih =>
      rw [Finset.sum_insert hr]
      refine Matrix.PosSemidef.add ?_ ih
      simpa using hA.conjTranspose_mul_mul_same (krausAmpl k (V r))ᴴ

end Kraus

/-- **Choi–Jamiołkowski isomorphism.**  A linear map `Φ : M_N(ℂ) → M_M(ℂ)` is completely
positive if and only if its Choi matrix `∑ i, ∑ j, E_{ij} ⊗ Φ(E_{ij})` is positive
semidefinite. -/
