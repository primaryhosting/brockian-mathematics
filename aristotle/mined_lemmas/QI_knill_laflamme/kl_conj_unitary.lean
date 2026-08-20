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

lemma kl_conj_unitary {P : Matrix d d ℂ} {E : ι → Matrix d d ℂ} {c : ι → ι → ℂ}
    (hKL : ∀ i j, P * (E i)ᴴ * E j * P = c i j • P) (U : Matrix ι ι ℂ) (k l : ι) :
    P * (∑ i, U i k • E i)ᴴ * (∑ j, U j l • E j) * P = ((Uᴴ * Matrix.of c * U) k l) • P := by
  have expand : P * (∑ i, U i k • E i)ᴴ * (∑ j, U j l • E j) * P
      = ∑ i, ∑ j, (star (U i k) * U j l) • (P * (E i)ᴴ * E j * P) := by
    simp only [conjTranspose_sum, conjTranspose_smul, Finset.sum_mul, Finset.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring_nf
  rw [expand]
  simp only [hKL, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Finset.sum_mul,
    RCLike.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] [DecidableEq ι] in
/-- Composing a channel with a single Kraus operator. -/
