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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

-- Note: the header above is a plain block comment rather than a module docstring,
-- since Lean 4 does not allow a module docstring to precede the `import` lines.

namespace Brockian.FermatNumbers

open Nat

/-- The Fermat numbers `Fₙ = 2 ^ (2 ^ n) + 1` (Mathlib's `Nat.fermatNumber`). -/
local notation "F" => Nat.fermatNumber

/-!
## The main statement

`FermatPrimeBeyondFour`: there is a Fermat prime exceeding `4`.
-/

/-- **Fermat prime beyond four.** There exists a Fermat number `Fₙ = 2 ^ (2 ^ n) + 1`
which is greater than `4` and prime.  (Witness: `F 4 = 65537`.) -/
theorem FermatPrimeBeyondFour : ∃ n : ℕ, 4 < F n ∧ (F n).Prime := by
  refine ⟨4, ?_, ?_⟩ <;> · rw [show F 4 = 65537 by rfl]; norm_num

/-- All four of `F 1 = 5`, `F 2 = 17`, `F 3 = 257`, `F 4 = 65537` are Fermat primes
beyond `4`. -/
theorem fermatPrime_of_one_le_of_le_four {n : ℕ} (h1 : 1 ≤ n) (h4 : n ≤ 4) :
    4 < F n ∧ (F n).Prime := by
  interval_cases n <;>
    refine ⟨?_, ?_⟩ <;>
    first
      | (rw [show F 1 = 5 by rfl]; norm_num)
      | (rw [show F 2 = 17 by rfl]; norm_num)
      | (rw [show F 3 = 257 by rfl]; norm_num)
      | (rw [show F 4 = 65537 by rfl]; norm_num)

/-!
## The open reading: a Fermat prime beyond *index* four

No Fermat prime `Fₙ` with `n > 4` is known, and it is conjectured that none exists.
We record the statement and prove several equivalent reformulations and
conditional reductions, together with the composite verdict for `F 5` and `F 6`.
-/

/-- The (open) statement that some Fermat number of index greater than `4` is prime. -/
def FermatPrimeBeyondIndexFour : Prop := ∃ n : ℕ, 4 < n ∧ (F n).Prime

/-- Contrapositive reformulation of `FermatPrimeBeyondIndexFour`. -/
theorem fermatPrimeBeyondIndexFour_iff_not_all_composite :
    FermatPrimeBeyondIndexFour ↔ ¬ ∀ n : ℕ, 4 < n → ¬ (F n).Prime := by
  unfold FermatPrimeBeyondIndexFour
  push_neg
  simp

/-- Reformulation via the minimal prime factor: `Fₙ` is prime iff it is its own least
prime factor. -/
theorem fermatPrimeBeyondIndexFour_iff_minFac :
    FermatPrimeBeyondIndexFour ↔ ∃ n : ℕ, 4 < n ∧ (F n).minFac = F n := by
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, hn, (Nat.prime_def_minFac.mp hp).2⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have h2 : 2 ≤ F n := (Nat.two_lt_fermatNumber n).le
    exact Nat.prime_def_minFac.mpr ⟨h2, h⟩

/-- **Reduction to Pépin's test.** If for some `n > 4` we have `3 ^ ((Fₙ - 1) / 2) = -1`
in `ZMod Fₙ`, then there is a Fermat prime beyond index four. -/
theorem fermatPrimeBeyondIndexFour_of_pepin
    (h : ∃ n : ℕ, 4 < n ∧ (3 : ZMod (F n)) ^ ((F n - 1) / 2) = -1) :
    FermatPrimeBeyondIndexFour := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, hn, Nat.pepin_primality' n h⟩

/-- **Reduction to a divisor search.** For `n > 1`, `Fₙ` fails to be prime exactly when it
has a proper divisor of the special form `k * 2 ^ (n + 2) + 1` with `k ≥ 1`. -/
theorem not_prime_fermatNumber_iff_exists_special_divisor {n : ℕ} (hn : 1 < n) :
    ¬ (F n).Prime ↔
      ∃ k : ℕ, 1 ≤ k ∧ (k * 2 ^ (n + 2) + 1) ∣ F n ∧ k * 2 ^ (n + 2) + 1 < F n := by
  have hF2 : 2 < F n := Nat.two_lt_fermatNumber n
  constructor
  · intro hnp
    set p := (F n).minFac with hp_def
    have hFne1 : F n ≠ 1 := Nat.fermatNumber_ne_one n
    have hp : p.Prime := Nat.minFac_prime hFne1
    have hpdvd : p ∣ F n := Nat.minFac_dvd _
    have hplt : p < F n := by
      rcases lt_or_eq_of_le (Nat.le_of_dvd (by lia) hpdvd) with h | h
      · exact h
      · exact absurd (h ▸ hp) hnp
    obtain ⟨k, hk⟩ := Nat.fermat_primeFactors_one_lt n p hn hp hpdvd
    refine ⟨k, ?_, hk ▸ hpdvd, hk ▸ hplt⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp at hk
      exact absurd (hk ▸ hp) (by norm_num)
    · exact hk1
  · rintro ⟨k, hk1, hdvd, hlt⟩ hp
    have h1 : k * 2 ^ (n + 2) + 1 ≠ 1 := by
      have : 0 < k * 2 ^ (n + 2) := Nat.mul_pos hk1 (Nat.two_pow_pos _)
      lia
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h | h
    · exact h1 h
    · lia

/-- `F 5 = 4294967297 = 641 * 6700417` is not prime. -/
theorem not_prime_fermatNumber_five : ¬ (F 5).Prime := by
  rw [show F 5 = 4294967297 by rfl]
  norm_num

/-- `F 6 = 18446744073709551617 = 274177 * 67280421310721` is not prime. -/
theorem not_prime_fermatNumber_six : ¬ (F 6).Prime := by
  intro hp
  have hdvd : (274177 : ℕ) ∣ F 6 := by
    rw [show F 6 = 18446744073709551617 by rfl]
    exact ⟨67280421310721, by norm_num⟩
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · norm_num at h
  · rw [show F 6 = 18446744073709551617 by rfl] at h
    norm_num at h

end Brockian.FermatNumbers

