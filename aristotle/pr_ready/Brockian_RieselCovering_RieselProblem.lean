/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- The Riesel number under consideration. -/
def k : ℕ := 509203

/-- The product of the covering set `{3, 5, 7, 13, 17, 241}`.  It equals `2 ^ 24 - 1`. -/
def M : ℕ := 5592405

/-- For a residue `r`, the prime of the covering set that divides `k * 2 ^ r - 1`
whenever `n ≡ r [MOD 24]`. -/
def covPrime (r : ℕ) : ℕ :=
  [3, 5, 3, 241, 3, 5, 3, 13, 3, 5, 3, 7, 3, 5, 3, 17, 3, 5, 3, 13, 3, 5, 3, 7].getD (r % 24) 3

lemma covPrime_dvd_M (r : ℕ) : covPrime r ∣ M := by
  have h : r % 24 < 24 := Nat.mod_lt _ (by norm_num)
  unfold covPrime
  interval_cases h' : (r % 24) <;> decide

lemma covPrime_bounds (r : ℕ) : 3 ≤ covPrime r ∧ covPrime r ≤ 241 := by
  have h : r % 24 < 24 := Nat.mod_lt _ (by norm_num)
  unfold covPrime
  interval_cases h' : (r % 24) <;> exact ⟨by norm_num, by norm_num⟩

lemma key_modEq (r : ℕ) (hr : r < 24) : k * 2 ^ r ≡ 1 [MOD covPrime r] := by
  unfold Nat.ModEq covPrime k
  interval_cases r <;> decide

lemma two_pow_modEq (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 24) [MOD M] := by
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD M] := by decide
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  calc ((2 : ℕ) ^ 24) ^ (n / 24) * 2 ^ (n % 24)
      ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD M] := Nat.ModEq.mul (h24.pow _) rfl
    _ = 2 ^ (n % 24) := by ring

/-- The covering argument: for every `n`, one of the six primes of the covering set
`{3, 5, 7, 13, 17, 241}` divides `509203 * 2 ^ n - 1`. -/
theorem covPrime_dvd (n : ℕ) : covPrime (n % 24) ∣ k * 2 ^ n - 1 := by
  have hd : covPrime (n % 24) ∣ M := covPrime_dvd_M _
  have h1 : k * 2 ^ n ≡ k * 2 ^ (n % 24) [MOD covPrime (n % 24)] :=
    Nat.ModEq.of_dvd hd ((two_pow_modEq n).mul_left k)
  have h2 : k * 2 ^ (n % 24) ≡ 1 [MOD covPrime (n % 24)] :=
    key_modEq _ (Nat.mod_lt _ (by norm_num))
  have h3 : (1 : ℕ) ≡ k * 2 ^ n [MOD covPrime (n % 24)] := (h1.trans h2).symm
  have hle : (1 : ℕ) ≤ k * 2 ^ n := Nat.mul_pos (by norm_num [k]) (Nat.two_pow_pos n)
  exact (Nat.modEq_iff_dvd' hle).mp h3

/-- **The Riesel problem**: `509203` is a Riesel number, i.e. `509203 * 2 ^ n - 1` is
composite (never prime) for every `n ≥ 1`. -/
theorem RieselProblem (n : ℕ) (hn : 1 ≤ n) : ¬ Nat.Prime (509203 * 2 ^ n - 1) := by
  intro hp
  have hdvd : covPrime (n % 24) ∣ 509203 * 2 ^ n - 1 := covPrime_dvd n
  obtain ⟨hp3, hp241⟩ := covPrime_bounds (n % 24)
  have hbig : 1018405 ≤ 509203 * 2 ^ n - 1 := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simp only [pow_one] at h2
    have : 509203 * 2 ≤ 509203 * 2 ^ n := Nat.mul_le_mul_left _ h2
    omega
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

end Brockian.RieselCovering

