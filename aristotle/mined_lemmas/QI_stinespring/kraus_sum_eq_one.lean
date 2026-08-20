/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/

lemma kraus_sum_eq_one [Fintype A] [DecidableEq A] [Fintype B] {R : Type*} [Fintype R]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} {K : R → Matrix B A ℂ}
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ) (hTP : IsTracePreserving Φ) :
    ∑ s, (K s)ᴴ * K s = 1 := by
  classical
  ext i j
  have h := hTP (single j i 1)
  rw [hK] at h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ite_and] at h ⊢
  rw [← h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Any isometry extends to a unitary between spaces of equal dimension: if the columns
of `W` are orthonormal and `f` embeds the column index type into `Z` with
`card Z = card Y`, then `W` consists of columns of a unitary matrix. -/
