import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma twinCount_two_pow_bound {m : ℕ} (hm : 1024 ≤ m) :
    (twinCount (2 ^ m) : ℝ) / 2 ^ m
      ≤ 2 / 2 ^ (m / 2) + 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
        + Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4 + 21 * (m : ℝ) ^ 41 / 2 ^ (m / 2) := by
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 m := ⟨_, rfl⟩
  rw [← hl]
  have hl10 : 10 ≤ l := by
    have h1 : Nat.log 2 1024 ≤ Nat.log 2 m := Nat.log_mono_right hm
    have h2 : Nat.log 2 1024 = 10 := by norm_num
    omega
  have hpowl : 2 ^ l ≤ m := by
    rw [hl]
    exact Nat.pow_log_le_self 2 (by omega)
  have hpowl2 : m < 2 * 2 ^ l := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) m
    rw [← hl] at h
    calc m < 2 ^ (l + 1) := h
      _ = 2 * 2 ^ l := by ring
  have h80 : 80 * l ≤ m := le_trans (eighty_mul_le_two_pow hl10) hpowl
  obtain ⟨q, hq⟩ : ∃ q, q = m / (40 * l) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hqm : 40 * l * q ≤ m := by
    rw [hq]
    exact Nat.mul_div_le m (40 * l)
  have hqup : m < (q + 1) * (40 * l) := by
    rw [← Nat.div_lt_iff_lt_mul (show 0 < 40 * l by omega), ← hq]
    omega
  exact twinCount_two_pow_bound_gen hm hl10 hpowl hpowl2 hq2 hqm hqup

