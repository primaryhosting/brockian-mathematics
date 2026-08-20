/-!
# Quadruplet 11 13 17 19
Category: Frontier — Prime Numbers
Target: Constellation.quadruplet_11_13_17_19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Constellation

/-- Primality of a natural number, spelled out elementarily: `n` is at least `2`
and every divisor of `n` is either `1` or `n`.

This is stated without any `import` because Lean requires every `import` command to
precede all other syntax in a file, including the module docstring above; the file
`RequestProject/Quadruplet11131719Mathlib.lean` proves that `IsPrimeNat` is equivalent
to Mathlib's `Nat.Prime`, and restates the theorem below in those terms. -/

theorem isPrimeNat_iff_nat_prime (n : Nat) : IsPrimeNat n ↔ Nat.Prime n :=
  ⟨fun ⟨h2, h⟩ => (Nat.prime_def.2 ⟨h2, h⟩), fun hp => ⟨hp.two_le, fun _ hm => (Nat.Prime.eq_one_or_self_of_dvd hp _ hm)⟩⟩

/-- Mathlib-flavoured restatement: `(11, 13, 17, 19)` is a prime quadruplet with
pattern `(0, 2, 6, 8)`. -/
