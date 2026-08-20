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

lemma outer_quadratic (v w : d → ℂ) :
    star w ⬝ᵥ (vecMulVec v (star v) *ᵥ w) = star (star w ⬝ᵥ v) * (star w ⬝ᵥ v) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq d] in
