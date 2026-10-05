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

/-
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering set assignment: for a residue `r` of the exponent modulo `36`,
`coverPrime r` is a prime from Selfridge's covering set
`{3, 5, 7, 13, 19, 37, 73}` that divides `78557 * 2 ^ n + 1` whenever `n % 36 = r`. -/
def coverPrime (r : ℕ) : ℕ :=
  ([3, 5, 3, 73, 3, 5, 3, 7, 3, 5, 3, 13, 3, 5, 3, 19, 3, 5, 3, 7,
    3, 5, 3, 13, 3, 5, 3, 37, 3, 5, 3, 7, 3, 5, 3, 13] : List ℕ).getD r 3

/-- Outside the range of residues the lookup returns the default value `3`. -/
lemma coverPrime_of_ge (r : ℕ) (hr : 36 ≤ r) : coverPrime r = 3 := by
  unfold coverPrime
  rw [List.getD_eq_default _ _ (by simpa using hr)]

/-- Every value of `coverPrime` is at least `3` (in particular it is not a unit). -/
lemma three_le_coverPrime (r : ℕ) : 3 ≤ coverPrime r := by
  have h : ∀ s < 36, 3 ≤ coverPrime s := by decide
  rcases lt_or_ge r 36 with hr | hr
  · exact h r hr
  · rw [coverPrime_of_ge r hr]

/-- Every value of `coverPrime` is at most `73`. -/
lemma coverPrime_le (r : ℕ) : coverPrime r ≤ 73 := by
  have h : ∀ s < 36, coverPrime s ≤ 73 := by decide
  rcases lt_or_ge r 36 with hr | hr
  · exact h r hr
  · rw [coverPrime_of_ge r hr]; norm_num

/-- Each prime of the covering set has multiplicative order dividing `36`,
i.e. it divides `2 ^ 36 - 1`. -/
lemma two_pow_36_modEq_one (r : ℕ) (hr : r < 36) :
    (2 : ℕ) ^ 36 ≡ 1 [MOD coverPrime r] := by
  have h : ∀ s < 36, 2 ^ 36 % coverPrime s = 1 % coverPrime s := by decide
  exact h r hr

/-- Since `2 ^ 36 ≡ 1`, the powers of two modulo a covering prime are `36`-periodic. -/
lemma two_pow_modEq (r n : ℕ) (hr : r < 36) :
    (2 : ℕ) ^ n ≡ 2 ^ (n % 36) [MOD coverPrime r] := by
  conv_lhs => rw [← Nat.div_add_mod n 36, pow_add, pow_mul]
  calc ((2 : ℕ) ^ 36) ^ (n / 36) * 2 ^ (n % 36)
      ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD coverPrime r] :=
        Nat.ModEq.mul_right _ (Nat.ModEq.pow _ (two_pow_36_modEq_one r hr))
    _ = 2 ^ (n % 36) := by rw [one_pow, one_mul]

/-- The covering property: for every `n`, the prime `coverPrime (n % 36)` divides
`78557 * 2 ^ n + 1`. -/
theorem coverPrime_dvd (n : ℕ) : coverPrime (n % 36) ∣ 78557 * 2 ^ n + 1 := by
  have hr : n % 36 < 36 := Nat.mod_lt _ (by norm_num)
  have hbase : ∀ s < 36, (78557 * 2 ^ s + 1) % coverPrime s = 0 := by decide
  have key : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD coverPrime (n % 36)] :=
    Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (two_pow_modEq (n % 36) n hr))
  have h0 : (78557 * 2 ^ (n % 36) + 1) % coverPrime (n % 36) = 0 := hbase _ hr
  exact (Nat.modEq_zero_iff_dvd).1
    (key.trans (Nat.modEq_zero_iff_dvd.2 (Nat.dvd_of_mod_eq_zero h0)))

/-- **The Sierpinski problem (Selfridge's covering argument).**
`78557` is a Sierpiński number: for every natural number `n`, the number
`78557 * 2 ^ n + 1` is composite, i.e. never prime. -/
theorem SierpinskiProblem (n : ℕ) : ¬ Nat.Prime (78557 * 2 ^ n + 1) := by
  intro hp
  have hdvd : coverPrime (n % 36) ∣ 78557 * 2 ^ n + 1 := coverPrime_dvd n
  have h3 : 3 ≤ coverPrime (n % 36) := three_le_coverPrime _
  have h73 : coverPrime (n % 36) ≤ 73 := coverPrime_le _
  have hbig : 78557 < 78557 * 2 ^ n + 1 := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    nlinarith
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

end SierpinskiCovering
end Brockian

