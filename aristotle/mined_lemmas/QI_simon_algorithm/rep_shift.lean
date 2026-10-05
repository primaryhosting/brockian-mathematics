/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma rep_shift (s x : BV n) : rep s (x + s) = rep s x := by
  unfold rep
  rw [BV.add_add_cancel]
  by_cases h : ord x ≤ ord (x + s)
  · by_cases h' : ord (x + s) ≤ ord x
    · have : x = x + s := ord_injective (le_antisymm h h')
      simp [← this]
    · simp [h, h']
  · have h' : ord (x + s) ≤ ord x := le_of_not_ge h
    simp [h, h']

/-- The adversary's oracle: two-to-one with hidden shift `s`, but equal to the identity on
the queried set `Q`, provided `Q` contains no pair differing by `s`. -/
