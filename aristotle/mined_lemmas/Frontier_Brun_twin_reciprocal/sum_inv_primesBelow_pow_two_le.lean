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

lemma sum_inv_primesBelow_pow_two_le {q : ℕ} (hq : 1 ≤ q) :
    ∑ p ∈ Nat.primesBelow (2 ^ q + 1), (1 / (p : ℝ)) ≤ 5 + 4 * Real.log q := by
  have key : ∀ r : ℕ, 1 ≤ r →
      ∑ p ∈ Nat.primesBelow (2 ^ r + 1), (1 / (p : ℝ))
        ≤ 1 / 2 + 4 * ((harmonic (r - 1) : ℚ) : ℝ) := by
    intro r hr
    induction r with
    | zero => omega
    | succ r ih =>
        rcases Nat.eq_zero_or_pos r with rfl | hr1
        · norm_num
          rw [show Nat.primesBelow 3 = {2} by decide]
          norm_num
        · have hstep := sum_inv_primesBelow_pow_two_step r hr1
          have hih := ih hr1
          have hharm : ((harmonic r : ℚ) : ℝ)
              = ((harmonic (r - 1) : ℚ) : ℝ) + 1 / (r : ℝ) := by
            obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            rw [harmonic_succ]
            push_cast
            ring
          simp only [Nat.add_sub_cancel]
          rw [hharm]
          have : (4 : ℝ) / r = 4 * (1 / (r : ℝ)) := by ring
          linarith [hstep, hih, this]
  have hkey := key q hq
  have hbound : ((harmonic (q - 1) : ℚ) : ℝ) ≤ 1 + Real.log q := by
    have h1 := harmonic_le_one_add_log (q - 1)
    have h2 : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
      rcases Nat.eq_zero_or_pos (q - 1) with h | h
      · rw [h]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hq)
      · apply Real.log_le_log (by exact_mod_cast h)
        have : (q - 1 : ℕ) ≤ q := by omega
        exact_mod_cast this
    linarith
  linarith

/-! ### The two products appearing in the sieve -/

