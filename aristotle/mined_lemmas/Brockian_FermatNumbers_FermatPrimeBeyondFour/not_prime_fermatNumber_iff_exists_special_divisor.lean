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
