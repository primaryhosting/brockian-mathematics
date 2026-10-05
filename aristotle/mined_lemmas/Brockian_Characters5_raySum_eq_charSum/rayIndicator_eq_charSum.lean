import Mathlib

/-!
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` valued in `ℂ`. -/

theorem rayIndicator_eq_charSum (n : ℕ) (r : ZMod 5) :
    (if (n : ZMod 5) = r then (1 : ℂ) else 0)
      = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  rw [sum_e_mul]
  by_cases h : (n : ZMod 5) = r
  · simp [h]
  · rw [if_neg h, if_neg (by simpa [sub_eq_zero] using h)]
    ring

/-- The number of elements of `S` lying on the ray `r` modulo `5`.

The binder type `n : ℕ` is stated explicitly: writing `fun n => (n : ZMod 5) = r` makes Lean read
`(n : ZMod 5)` as a type ascription, giving the binder type `ZMod 5` and silently coercing `S` to
`Finset (ZMod 5)` (i.e. taking its image), which would count residues rather than elements of `S`. -/
