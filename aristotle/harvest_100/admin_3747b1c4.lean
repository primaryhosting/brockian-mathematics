import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib
import Brockian.RieselCovering

/-!
# Riesel problem, Mathlib-facing statement

`Brockian.RieselCovering` must begin with a mandated header comment, which forces it to be
import-free (Lean requires `import`s to come first in a file).  This module imports Mathlib and
restates the main result using Mathlib's `Nat.Prime`.
-/

namespace Brockian
namespace RieselCovering

theorem isPrimeNat_of_prime {m : Nat} (hm : Nat.Prime m) : IsPrimeNat m :=
  ⟨hm.two_le, fun d hd => hm.eq_one_or_self_of_dvd d hd⟩

/-- For every `n ≥ 1`, `509203 * 2 ^ n - 1` is not prime (Mathlib's `Nat.Prime`). -/
theorem riesel_509203_not_prime (n : ℕ) (hn : 1 ≤ n) : ¬ Nat.Prime (509203 * 2 ^ n - 1) :=
  fun h => RieselProblem n hn (isPrimeNat_of_prime h)

/-- For every `n ≥ 1`, `509203 * 2 ^ n - 1` is composite: it has a nontrivial divisor. -/
theorem riesel_509203_composite (n : ℕ) (hn : 1 ≤ n) :
    ∃ d, d ∣ 509203 * 2 ^ n - 1 ∧ 1 < d ∧ d < 509203 * 2 ^ n - 1 := by
  have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbig : 1 < 509203 * 2 ^ n - 1 := by simp only [pow_one] at h2; omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := 509203 * 2 ^ n - 1) (by omega)
  refine ⟨p, hpd, hp.one_lt, ?_⟩
  rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hpd) with h | h
  · exact h
  · exact absurd (h ▸ hp) (riesel_509203_not_prime n hn)

end RieselCovering
end Brockian

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE ON IMPORTS: Lean requires `import` commands to precede every other command,
-- including module docstrings such as the mandated header above.  The development below is
-- therefore written so that it needs no imports at all (only Lean's automatic `Init`).
-- The companion module `Brockian.RieselCoveringMathlib` imports Mathlib and restates the
-- main theorem with Mathlib's `Nat.Prime`.

namespace Brockian
namespace RieselCovering

/-- Primality of a natural number, spelled out (equivalent to Mathlib's `Nat.Prime`;
see `Brockian.RieselCoveringMathlib`). -/
def IsPrimeNat (m : Nat) : Prop :=
  2 ≤ m ∧ ∀ d, d ∣ m → d = 1 ∨ d = m

/-- `k` is a *Riesel number*: it is odd, positive, and `k * 2 ^ n - 1` is never prime for
`n ≥ 1`. -/
def IsRieselNumber (k : Nat) : Prop :=
  k % 2 = 1 ∧ 0 < k ∧ ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (k * 2 ^ n - 1)

/-- Covering-set step.  If `p` divides `2 ^ 24 - 1 = 16777215` (so `2` has order dividing `24`
modulo `p`) and `p` divides `509203 * 2 ^ r - 1`, then `p` divides `509203 * 2 ^ n - 1` for
every `n ≡ r [MOD 24]`. -/
theorem cover_dvd (p r : Nat) (hp24 : p ∣ 16777215) (hr : p ∣ 509203 * 2 ^ r - 1) :
    ∀ q : Nat, p ∣ 509203 * 2 ^ (24 * q + r) - 1 := by
  intro q
  induction q with
  | zero => simpa using hr
  | succ q ih =>
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    have hpow : (2 : Nat) ^ (24 * (q + 1) + r) = 16777216 * 2 ^ (24 * q + r) := by
      rw [← h24, ← Nat.pow_add]; congr 1; omega
    have hone : 1 ≤ (2 : Nat) ^ (24 * q + r) := Nat.one_le_two_pow
    have key : 509203 * 2 ^ (24 * (q + 1) + r) - 1
        = 16777216 * (509203 * 2 ^ (24 * q + r) - 1) + 16777215 := by
      rw [hpow]; omega
    rw [key]
    exact Nat.dvd_add (Nat.dvd_trans ih (Nat.dvd_mul_left _ _)) hp24

/-- **The Riesel problem.**  For every `n ≥ 1` the number `509203 * 2 ^ n - 1` is not prime.

The proof uses the covering set `{3, 5, 7, 13, 17, 241}`; each of these primes divides
`2 ^ 24 - 1 = 16777215`, and for each residue `r < 24` one of them divides
`509203 * 2 ^ r - 1`. -/
theorem RieselProblem : ∀ n : Nat, 1 ≤ n → ¬ IsPrimeNat (509203 * 2 ^ n - 1) := by
  intro n hn hprime
  have h2 : (2 : Nat) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hbig : 241 < 509203 * 2 ^ n - 1 := by simp only [Nat.pow_one] at h2; omega
  have step : ∀ p r : Nat, 1 < p → p ≤ 241 → p ∣ 16777215 →
      p ∣ 509203 * 2 ^ r - 1 → n = 24 * (n / 24) + r → False := by
    intro p r hp1 hple hp24 hr hnr
    have hd : p ∣ 509203 * 2 ^ n - 1 := by
      rw [hnr]; exact cover_dvd p r hp24 hr (n / 24)
    rcases hprime.2 p hd with h | h <;> omega
  have hcase : n % 24 = 0 ∨ n % 24 = 1 ∨ n % 24 = 2 ∨ n % 24 = 3 ∨ n % 24 = 4 ∨
      n % 24 = 5 ∨ n % 24 = 6 ∨ n % 24 = 7 ∨ n % 24 = 8 ∨ n % 24 = 9 ∨ n % 24 = 10 ∨
      n % 24 = 11 ∨ n % 24 = 12 ∨ n % 24 = 13 ∨ n % 24 = 14 ∨ n % 24 = 15 ∨ n % 24 = 16 ∨
      n % 24 = 17 ∨ n % 24 = 18 ∨ n % 24 = 19 ∨ n % 24 = 20 ∨ n % 24 = 21 ∨ n % 24 = 22 ∨
      n % 24 = 23 := by omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h
  · exact step 3 0 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 1 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 2 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 241 3 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 4 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 5 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 6 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 13 7 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 8 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 9 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 10 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 7 11 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 12 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 13 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 14 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 17 15 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 16 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 17 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 18 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 13 19 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 20 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 5 21 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 3 22 (by omega) (by omega) (by decide) (by decide) (by omega)
  · exact step 7 23 (by omega) (by omega) (by decide) (by decide) (by omega)

/-- `509203` is a Riesel number. -/
theorem isRieselNumber_509203 : IsRieselNumber 509203 :=
  ⟨by decide, by omega, RieselProblem⟩

/-- Riesel numbers exist. -/
theorem exists_rieselNumber : ∃ k : Nat, IsRieselNumber k :=
  ⟨509203, isRieselNumber_509203⟩

end RieselCovering
end Brockian

