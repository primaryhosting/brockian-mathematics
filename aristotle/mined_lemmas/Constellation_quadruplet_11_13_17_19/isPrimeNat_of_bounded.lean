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

theorem isPrimeNat_of_bounded {n : Nat} (h2 : 2 ≤ n)
    (h : ∀ m, m < n + 1 → m ∣ n → m = 1 ∨ m = n) : IsPrimeNat n := by
  refine ⟨h2, fun m hm => h m ?_ hm⟩
  exact Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hm)

/-- `(11, 13, 17, 19)` is a prime quadruplet of pattern `(0, 2, 6, 8)`: each of
`11`, `13`, `17`, `19` is prime, and `13 = 11 + 2`, `17 = 11 + 6`, `19 = 11 + 8`. -/
