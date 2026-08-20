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

lemma poly_div_two_pow_half_le (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → (m : ℝ) ^ A / 2 ^ (m / 2) ≤ C / (m : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := poly_le_geom (A + 2)
  refine ⟨3 ^ (A + 2) * C, by positivity, fun m hm => ?_⟩
  set t := m / 2 with ht
  have ht1 : 1 ≤ t := by omega
  have hmt : m ≤ 3 * t := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h1 : (m : ℝ) ^ (A + 2) ≤ (3 * t : ℝ) ^ (A + 2) := by
    apply pow_le_pow_left₀ (le_of_lt hmR)
    exact_mod_cast hmt
  have h2 : (3 * t : ℝ) ^ (A + 2) = 3 ^ (A + 2) * (t : ℝ) ^ (A + 2) := by rw [mul_pow]
  have h3 : (m : ℝ) ^ (A + 2) ≤ 3 ^ (A + 2) * C * 2 ^ t := by
    have := hC t
    nlinarith [pow_pos (show (0:ℝ) < 3 by norm_num) (A + 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc (m : ℝ) ^ A * (m : ℝ) ^ 2 = (m : ℝ) ^ (A + 2) := by rw [← pow_add]
    _ ≤ 3 ^ (A + 2) * C * 2 ^ t := h3

