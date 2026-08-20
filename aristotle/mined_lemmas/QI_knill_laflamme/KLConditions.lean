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

def KLConditions (P : Matrix d d ℂ) (E : ι → Matrix d d ℂ) : Prop :=
  ∃ c : ι → ι → ℂ, ∀ i j, P * (E i)ᴴ * E j * P = c i j • P

/-- The code with orthogonal projector `P` **corrects** the error set `E` if there is a
recovery channel, given by Kraus operators `R k` with `∑ k, (R k)ᴴ * (R k) = 1`, which
undoes the error channel `ρ ↦ ∑ i, E i * ρ * (E i)ᴴ` on all states supported on the code. -/
