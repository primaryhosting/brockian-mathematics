import Mathlib
import RequestProject.Main

/-!
Mathlib-flavoured restatement of the main result: `73` is a prime that is a sum of two squares.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`. -/
theorem two_squares_73_prime : Nat.Prime 73 ∧ ∃ a b : ℕ, (73 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_73.2⟩

end Math

/-!
# Two Squares 73
Category: Pure Mathematics
Target: Math.two_squares_73
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

/--
**Two squares for 73.**

`73` is a prime number (its only divisors are `1` and `73`) and it is a sum of two squares,
namely `73 = 3 ^ 2 + 8 ^ 2`.

The primality is stated elementarily (`∀ d, d ∣ 73 → d = 1 ∨ d = 73`) so that the statement
is self-contained; see `Math.two_squares_73_prime` for the version phrased with `Nat.Prime`.
-/
theorem two_squares_73 :
    (∀ d : Nat, d ∣ 73 → d = 1 ∨ d = 73) ∧ ∃ a b : Nat, (73 : Nat) = a ^ 2 + b ^ 2 := by
  refine ⟨?_, 3, 8, rfl⟩
  have key : ∀ d : Nat, d < 74 → d ∣ 73 → d = 1 ∨ d = 73 := by decide
  intro d hd
  exact key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)) hd

end Math

