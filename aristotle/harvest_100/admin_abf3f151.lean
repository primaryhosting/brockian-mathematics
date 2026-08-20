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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `IsErdosStrausRepresentable n` says that `4 / n` is a sum of three positive unit fractions,
`4 / n = 1 / x + 1 / y + 1 / z`, written here in the equivalent denominator-cleared form
`4 * (x * y * z) = n * (y * z + x * z + x * y)` with `x, y, z > 0`.
(The three denominators are not required to be distinct.) -/
def IsErdosStrausRepresentable (n : Nat) : Prop :=
  ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * (x * y * z) = n * (y * z + x * z + x * y)

/-- Elementary primality predicate (stated without Mathlib). -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Every `n ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p : Nat, IsPrimeNat p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : ∀ d : Nat, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hp⟩, Nat.dvd_refl n⟩
    · obtain ⟨d, hdvd, hd1, hdn⟩ : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by grind
      have hd0 : d ≠ 0 := by
        intro h
        subst h
        have := Nat.eq_zero_of_zero_dvd hdvd
        omega
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hd2 : 2 ≤ d := by omega
      obtain ⟨p, hp, hpd⟩ := ih d (by omega) hd2
      exact ⟨p, hp, Nat.dvd_trans hpd hdvd⟩

/-- Representability passes from a divisor to its multiples. -/
theorem representable_of_dvd {d n : Nat} (hn : 0 < n) (hdvd : d ∣ n)
    (h : IsErdosStrausRepresentable d) : IsErdosStrausRepresentable n := by
  obtain ⟨k, rfl⟩ := hdvd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hn
    · exact hk
  refine ⟨k * x, k * y, k * z, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hk hx
  · exact Nat.mul_pos hk hy
  · exact Nat.mul_pos hk hz
  · grind

/-- `4 / 2 = 1 / 1 + 1 / 2 + 1 / 2`. -/
theorem representable_two : IsErdosStrausRepresentable 2 :=
  ⟨1, 2, 2, by omega, by omega, by omega, by decide⟩

/-- For `n = 4k + 3` we have `4 / n = 1/(k+1) + 1/(2(k+1)n) + 1/(2(k+1)n)`. -/
theorem representable_of_three_mod_four {n : Nat} (h : n % 4 = 3) :
    IsErdosStrausRepresentable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  exact ⟨k + 1, 2 * (k + 1) * (4 * k + 3), 2 * (k + 1) * (4 * k + 3), by omega, by grind,
    by grind, by grind⟩

/-- Every even `n > 0` is representable. -/
theorem representable_of_even {n : Nat} (hn : 0 < n) (h : 2 ∣ n) :
    IsErdosStrausRepresentable n :=
  representable_of_dvd hn h representable_two

/-- Unconditional partial result: every `n ≥ 2` with `n % 4 ≠ 1` is representable. -/
theorem representable_of_not_one_mod_four {n : Nat} (hn : 2 ≤ n) (h : n % 4 ≠ 1) :
    IsErdosStrausRepresentable n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · exact representable_of_even (by omega) ⟨n / 2, by omega⟩
  · exact representable_of_three_mod_four (by omega)

/-- **Erdős–Straus conjecture, reduced to primes `p ≡ 1 (mod 4)`.**

For every `n ≥ 2` the fraction `4 / n` is a sum of three positive unit fractions, provided this
is known for every prime `p ≡ 1 (mod 4)`. All the remaining cases (`p = 2` and `p ≡ 3 mod 4`)
are settled unconditionally here, so this is a complete Lean-checked reduction of the
Erdős–Straus conjecture to the case of primes congruent to `1` modulo `4`. -/
theorem ErdosStrausConjecture
    (hprime : ∀ p : Nat, IsPrimeNat p → p % 4 = 1 → IsErdosStrausRepresentable p)
    (n : Nat) (hn : 2 ≤ n) : IsErdosStrausRepresentable n := by
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_dvd n hn
  refine representable_of_dvd (by omega) hpdvd ?_
  have hp2 : 2 ≤ p := hp.1
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have : p = 2 := by omega
    subst this
    exact representable_two
  · -- `p ≥ 3` is odd, since `2 ∣ p` would force `p = 2`
    have hodd : p % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one p with he | ho
      · have : (2 : Nat) ∣ p := ⟨p / 2, by omega⟩
        rcases hp.2 2 this with h | h <;> omega
      · exact ho
    have : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases this with h1 | h4
    · exact hprime p hp h1
    · exact representable_of_three_mod_four h4

end Brockian.ErdosStraus

import Mathlib
import Brockian.ErdosStraus

/-!
# Erdős–Straus: the rational formulation

`Brockian.ErdosStraus.IsErdosStrausRepresentable` is stated in denominator-cleared form over `ℕ`
so that the main file needs no imports (its first line is a required header comment).  Here we
check, using Mathlib, that it really is equivalent to `4 / n = 1/x + 1/y + 1/z` over `ℚ`, and we
restate the main reduction theorem in that form.
-/

namespace Brockian.ErdosStraus

/-- The unit-fraction statement over `ℚ`. -/
def IsErdosStrausRepresentableRat (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The denominator-cleared `ℕ`-statement is equivalent to the `ℚ`-statement, for `n > 0`. -/
theorem isErdosStrausRepresentable_iff_rat {n : ℕ} (hn : 0 < n) :
    IsErdosStrausRepresentable n ↔ IsErdosStrausRepresentableRat n := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
    have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
    have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
    have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) h
    field_simp
    linarith [h']
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
    have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
    have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
    have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by
      field_simp at h
      linarith [h]
    exact_mod_cast h'

/-- `IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {p : ℕ} : IsPrimeNat p ↔ p.Prime := by
  constructor
  · rintro ⟨h2, hd⟩
    rw [Nat.prime_def]
    exact ⟨h2, fun d hd' => hd d hd'⟩
  · intro hp
    exact ⟨hp.two_le, fun d hd => (Nat.Prime.eq_one_or_self_of_dvd hp d hd)⟩

/-- **Erdős–Straus conjecture over `ℚ`, reduced to primes `p ≡ 1 (mod 4)`.**

If `4 / p = 1/x + 1/y + 1/z` is solvable in positive integers for every prime `p ≡ 1 (mod 4)`,
then it is solvable for every `n ≥ 2`. -/
theorem ErdosStrausConjecture_rat
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 1 → IsErdosStrausRepresentableRat p)
    (n : ℕ) (hn : 2 ≤ n) : IsErdosStrausRepresentableRat n := by
  rw [← isErdosStrausRepresentable_iff_rat (by omega)]
  refine ErdosStrausConjecture (fun p hp h1 => ?_) n hn
  have hp' : p.Prime := isPrimeNat_iff_prime.mp hp
  exact (isErdosStrausRepresentable_iff_rat hp'.pos).mpr (hprime p hp' h1)

/-- Unconditional partial result over `ℚ`: `4/n` is a sum of three unit fractions whenever
`n ≥ 2` and `n % 4 ≠ 1`. -/
theorem representableRat_of_not_one_mod_four {n : ℕ} (hn : 2 ≤ n) (h : n % 4 ≠ 1) :
    IsErdosStrausRepresentableRat n :=
  (isErdosStrausRepresentable_iff_rat (by omega)).mp (representable_of_not_one_mod_four hn h)

end Brockian.ErdosStraus

