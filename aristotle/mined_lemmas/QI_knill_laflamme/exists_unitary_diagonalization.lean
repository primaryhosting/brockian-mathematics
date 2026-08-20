/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the required header is
-- repeated verbatim as the module docstring immediately below the import.)

import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
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

open Matrix ComplexOrder

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

/-! ## Definitions -/

/-- The **Knill–Laflamme conditions** for a code with orthogonal projector `P` and a set of
error operators `E i`: `P (E i)ᴴ (E j) P = c i j • P` for some matrix of scalars `c`. -/

lemma exists_unitary_diagonalization {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    ∃ (U : Matrix ι ι ℂ) (dd : ι → ℝ), (∀ i, 0 ≤ dd i) ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * C * U = diagonal (fun i => (dd i : ℂ)) ∧ C.trace = ∑ i, (dd i : ℂ) := by
  have hspec0 : C = (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      (diagonal (fun i => (hC.1.eigenvalues i : ℂ))) *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hC.1.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
  have hUsU0 : (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hC.1.eigenvectorUnitary
  have hUUs0 : (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hC.1.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hC.1.eigenvectorUnitary
  have htr0 : C.trace = ∑ i, (hC.1.eigenvalues i : ℂ) := hC.1.trace_eq_sum_eigenvalues
  have hnn0 : ∀ i, 0 ≤ hC.1.eigenvalues i := hC.eigenvalues_nonneg
  revert hspec0 hUsU0 hUUs0 htr0 hnn0
  generalize (hC.1.eigenvectorUnitary : Matrix ι ι ℂ) = U
  generalize hC.1.eigenvalues = dd
  intro hspec hUsU hUUs htr hnn
  refine ⟨U, dd, hnn, hUsU, hUUs, ?_, htr⟩
  calc Uᴴ * C * U = (Uᴴ * U) * (diagonal (fun i => (dd i : ℂ))) * (Uᴴ * U) := by
        rw [hspec]; simp [Matrix.mul_assoc]
    _ = diagonal (fun i => (dd i : ℂ)) := by rw [hUsU]; simp

/-- A unitary change of the Kraus operators does not change the channel. -/
