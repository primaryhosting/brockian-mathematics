/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime 41 is a sum of two squares.**

`41` is prime (it is at least `2` and its only divisors are `1` and `41`) and
`41 = 4 ^ 2 + 5 ^ 2`.

The fixed header comment above must be the first thing in this file, which makes an
`import` line illegal here, so primality is spelled out directly and the proof uses
only Lean's core library.  See `RequestProject/MathMathlib.lean` for the same fact
stated with Mathlib's `Nat.Prime` and derived from `Nat.Prime.sq_add_sq`. -/

theorem two_squares_41 :
    (2 ≤ 41 ∧ ∀ m : Nat, m ∣ 41 → m = 1 ∨ m = 41) ∧ ∃ a b : Nat, 41 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 4, 5, by decide⟩
  have h : ∀ m ≤ 41, m ∣ 41 → m = 1 ∨ m = 41 := by decide
  intro m hm
  exact h m (Nat.le_of_dvd (by decide) hm) hm

end Math

import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Companion to `RequestProject/Math.lean`.  The target theorem `Math.two_squares_41`
lives in a file that must begin with a fixed header comment, which prevents it from
carrying an `import` line, so it is stated and proved using only Lean's core library.
Here we record the same fact phrased with Mathlib's `Nat.Prime`, both by exhibiting the
explicit representation `41 = 4 ^ 2 + 5 ^ 2` and by invoking Fermat's two-squares
theorem `Nat.Prime.sq_add_sq` (applicable since `41 % 4 = 1 ≠ 3`).
-/

namespace Math

/-- `41` is prime and is a sum of two squares, namely `41 = 4 ^ 2 + 5 ^ 2`. -/
