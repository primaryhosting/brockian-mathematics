import Mathlib
import RequestProject.TwoSquares13

/-!
# Two Squares 13 (Mathlib phrasing)

A companion to `RequestProject/TwoSquares13.lean`, restating the result with
Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/

theorem two_squares_13_prime : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 :=
  ⟨(Nat.prime_def_lt.2 ⟨by norm_num, fun m hm hdvd => by
      rcases Math.divisors_13 m hdvd with h | h
      · exact h
      · omega⟩), 2, 3, by norm_num⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` commands to precede every other command in a file,
including module doc comments such as the mandated header above.  Since the header
must literally begin the file, this development is carried out in pure core Lean,
without importing Mathlib; primality of 13 is therefore spelled out explicitly
(`2 ≤ 13` together with the fact that every divisor of 13 is `1` or `13`).
-/

namespace Math

/-- Every divisor of `13` is `1` or `13`. -/
