/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.** The number `89` is prime (it is at least `2` and its only
divisors are `1` and itself) and it is a sum of two squares, namely `89 = 5 ^ 2 + 8 ^ 2`.

Primality is spelled out directly here rather than via `Nat.Prime`, because the required
file header must be the first item in the file, which prevents an `import` line.  The file
`RequestProject/TwoSquares89Prime.lean` shows that this spelling is exactly `Nat.Prime 89`. -/

theorem prime_89_iff : (2 ≤ 89 ∧ ∀ m : ℕ, m ∣ 89 → m = 1 ∨ m = 89) ↔ Nat.Prime 89 :=
  ⟨fun h => Nat.prime_def.2 ⟨h.1, h.2⟩,
   fun h => ⟨h.two_le, fun m hm => h.eq_one_or_self_of_dvd m hm⟩⟩

/-- **Two squares for 89**, stated with Mathlib's `Nat.Prime`. -/
