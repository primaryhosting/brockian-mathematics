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

lemma sum_unitary_kraus (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) (E : ι → Matrix d d ℂ)
    (ρ : Matrix d d ℂ) :
    ∑ k, (∑ i, U i k • E i) * ρ * (∑ i, U i k • E i)ᴴ = ∑ i, E i * ρ * (E i)ᴴ := by
  have hexp : ∀ k : ι, (∑ i, U i k • E i) * ρ * (∑ i, U i k • E i)ᴴ
      = ∑ i, ∑ j, (U i k * star (U j k)) • (E i * ρ * (E j)ᴴ) := by
    intro k
    rw [conjTranspose_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_smul]
    simp [smul_smul, mul_comm]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hcol : ∀ j : ι, ∑ k, (U i k * star (U j k)) • (E i * ρ * (E j)ᴴ)
      = ((U * Uᴴ) i j) • (E i * ρ * (E j)ᴴ) := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
  simp only [hcol, hU]
  simp [Matrix.one_apply]

omit [DecidableEq d] [DecidableEq ι] in
/-- The Knill–Laflamme conditions in a rotated Kraus basis. -/
