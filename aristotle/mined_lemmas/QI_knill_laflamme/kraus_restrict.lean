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

lemma kraus_restrict {P : Matrix d d ℂ} (hPh : Pᴴ = P) (X : Matrix d d ℂ) {ρ : Matrix d d ℂ}
    (hρ : P * ρ * P = ρ) : X * ρ * Xᴴ = (X * P) * ρ * (X * P)ᴴ := by
  have h1 : (X * P) * ρ * (X * P)ᴴ = X * (P * ρ * P) * Xᴴ := by
    rw [conjTranspose_mul, hPh]
    simp [Matrix.mul_assoc]
  rw [h1, hρ]

omit [DecidableEq d] in
/-- Conjugating by a real multiple of the projector. -/
