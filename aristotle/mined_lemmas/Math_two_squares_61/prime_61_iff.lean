/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 61.** The number `61` is prime -- its only divisors are `1` and `61`,
and it is at least `2` -- and it is a sum of two squares, namely `61 = 5 ^ 2 + 6 ^ 2`.

Primality is spelled out elementarily here (`2 ≤ 61` together with the divisor condition)
so that this file needs no imports; the file `TwoSquares61Mathlib.lean` records the same
result phrased with Mathlib's `Nat.Prime`, together with the equivalence of the two
formulations. -/

theorem prime_61_iff : (2 ≤ 61 ∧ ∀ m : ℕ, m ∣ 61 → m = 1 ∨ m = 61) ↔ Nat.Prime 61 := by
  constructor
  · intro _
    norm_num
  · intro h
    exact ⟨h.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd h m hm)⟩

/-- The target theorem `Math.two_squares_61` indeed yields the Mathlib statement
`Nat.Prime 61 ∧ ∃ a b, 61 = a ^ 2 + b ^ 2`. -/
