/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`. It is stated directly here because the required header
comment must be the very first thing in the file, which rules out any `import`
line, so `Nat.Prime` is not available. -/

theorem isPrimeNat_29 : IsPrimeNat 29 :=
  ⟨by omega, fun m hm => divisors_of_29_le m (Nat.le_of_dvd (by omega) hm) hm⟩

/-- Key intermediate lemma: `29` is the sum of the squares of `2` and `5`. -/
