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


theorem dotp_eq_zero_of_amp_ne_zero {f : BV n → BV n} {s : BV n} (h : IsSimon f s)
    (y v : BV n) (hy : amp f y v ≠ 0) : dotp s y = 0 := by
  rcases zmod2_cases (dotp s y) with h0 | h1
  · exact h0
  · exact absurd (amp_eq_zero_of_dotp_ne_zero h y v h1) hy

/-! ## Quantum part: `O(n)` outcomes determine `s` -/

/-- **Quantum query count.** For any hidden shift `s ≠ 0` there is a set `Y` of at most `n`
possible measurement outcomes (all orthogonal to `s`) which pins `s` down: the only vectors
orthogonal to all of `Y` are `0` and `s`.  Hence `O(n)` quantum queries suffice. -/
