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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem exists_prime_factor_sq_le :
    ∀ m : Nat, 2 ≤ m → ¬ IsPrime m → ∃ p, IsPrime p ∧ p ∣ m ∧ p * p ≤ m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm hnp
    by_cases hc : ∃ d, d < m ∧ 2 ≤ d ∧ d ∣ m
    · obtain ⟨d, hdlt, hd2, hdvd⟩ := hc
      -- helper: from a divisor `e` with `e * e ≤ m` we extract a prime factor
      have key : ∀ e, e ∣ m → 2 ≤ e → e < m → e * e ≤ m →
          ∃ p, IsPrime p ∧ p ∣ m ∧ p * p ≤ m := by
        intro e hed he2 helt hee
        by_cases hpe : IsPrime e
        · exact ⟨e, hpe, hed, hee⟩
        · obtain ⟨p, hp, hpd, hpp⟩ := ih e helt he2 hpe
          exact ⟨p, hp, Nat.dvd_trans hpd hed, Nat.le_trans hpp (Nat.le_of_lt helt)⟩
      obtain ⟨k, hmk⟩ : ∃ k, d * k = m := ⟨m / d, Nat.mul_div_cancel' hdvd⟩
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, Nat.mul_zero] at hmk; omega
        · exact h
      have hkdvd : k ∣ m := ⟨d, by rw [← hmk, Nat.mul_comm]⟩
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · have hk1 : k = 1 := by omega
          rw [hk1, Nat.mul_one] at hmk
          omega
        · exact h
      have hklt : k < m := by
        have : 2 * k ≤ d * k := Nat.mul_le_mul_right k hd2
        omega
      rcases Nat.le_total d k with hdk | hkd
      · have : d * d ≤ d * k := Nat.mul_le_mul_left d hdk
        exact key d hdvd hd2 hdlt (by omega)
      · have : k * k ≤ d * k := Nat.mul_le_mul_right k hkd
        exact key k hkdvd hk2 hklt (by omega)
    · exact absurd ⟨hm, fun d hd h2 hdvd => hc ⟨d, hd, h2, hdvd⟩⟩ hnp

/-- Every `m ≥ 2` has a prime factor. -/
