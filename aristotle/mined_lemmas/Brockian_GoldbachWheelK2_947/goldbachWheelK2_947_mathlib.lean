import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
# Goldbach Wheel K 2 947 — Mathlib interface

The target theorem `Brockian.GoldbachWheelK2_947` lives in the self-contained file
`RequestProject/GoldbachWheelK2_947.lean` (which carries no imports, since its header
comment must be the first thing in the file). Here we identify the primality notion used
there with Mathlib's `Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/

theorem goldbachWheelK2_947_mathlib (n : ℕ) (h4 : 4 ≤ n) (hle : n ≤ 2 * 947) (hev : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_947 n h4 hle (Nat.even_iff.mp hev)
  exact ⟨p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian

/-! ## Primality

This file is self-contained (it has no `import`s, since the header comment above must be the
first thing in the file), so primality is developed from scratch, in the standard way:
`IsPrimeNat p` says that `p ≥ 2` and the only divisors of `p` are `1` and `p`.
A companion file identifies this notion with Mathlib's `Nat.Prime`. -/

/-- `p` is prime: `p ≥ 2` and every divisor of `p` is `1` or `p`. -/
