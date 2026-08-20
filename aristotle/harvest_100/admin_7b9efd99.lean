/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- **Two distinct fractions with small denominators are far apart.**
If `s/r ≠ s'/r'` then they differ by at least `1/(r*r')`. -/
lemma abs_sub_div_ge {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') {s s' : ℕ}
    (hne : (s : ℝ) / r ≠ (s' : ℝ) / r') :
    1 / ((r : ℝ) * r') ≤ |(s : ℝ) / r - (s' : ℝ) / r'| := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hkey : (s : ℝ) / r - (s' : ℝ) / r' = ((s : ℝ) * r' - (s' : ℝ) * r) / ((r : ℝ) * r') := by
    field_simp
  have hZ : (s * r' : ℤ) - (s' * r : ℤ) ≠ 0 := by
    intro h
    apply hne
    have hR : (s : ℝ) * r' = (s' : ℝ) * r := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      linarith
    field_simp
    linarith
  have h1 : (1 : ℝ) ≤ |(s : ℝ) * r' - (s' : ℝ) * r| := by
    have hint : (1 : ℤ) ≤ |(s * r' : ℤ) - (s' * r : ℤ)| := Int.one_le_abs (by simpa using hZ)
    have : ((1 : ℤ) : ℝ) ≤ ((|(s * r' : ℤ) - (s' * r : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hint
    rw [Int.cast_abs] at this
    push_cast at this
    exact this
  rw [hkey, abs_div, abs_of_pos (by positivity : (0:ℝ) < (r : ℝ) * r')]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact h1

/-- **Uniqueness of the fraction recovered from a measurement.**
If two fractions with denominators at most `N` both lie within `1/(2Q)` of `c/Q`,
where `Q ≥ N^2`, then they are equal. This is the classical post-processing step
of Shor's algorithm (continued-fraction expansion of `c/Q`). -/
lemma frac_unique {N Q c : ℕ} {r r' s s' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    (hrN : r ≤ N) (hr'N : r' ≤ N) (hQ : ((N : ℝ)) ^ 2 ≤ Q) (hQ0 : 0 < Q)
    (h1 : |(c : ℝ) / Q - (s : ℝ) / r| < 1 / (2 * Q))
    (h2 : |(c : ℝ) / Q - (s' : ℝ) / r'| < 1 / (2 * Q)) :
    (s : ℝ) / r = (s' : ℝ) / r' := by
  by_contra hne
  have hQ0' : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrr : ((r : ℝ) * r') ≤ (N : ℝ) ^ 2 := by
    have h1' : (r : ℝ) ≤ N := by exact_mod_cast hrN
    have h2' : (r' : ℝ) ≤ N := by exact_mod_cast hr'N
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
    nlinarith
  have hlow := abs_sub_div_ge hr hr' hne
  have hhigh : |(s : ℝ) / r - (s' : ℝ) / r'| < 1 / Q := by
    have hsum : |(s : ℝ) / r - (s' : ℝ) / r'| ≤
        |(s : ℝ) / r - (c : ℝ) / Q| + |(c : ℝ) / Q - (s' : ℝ) / r'| :=
      abs_sub_le _ _ _
    have hswap : |(s : ℝ) / r - (c : ℝ) / Q| = |(c : ℝ) / Q - (s : ℝ) / r| := abs_sub_comm _ _
    have heq : 1 / (2 * (Q : ℝ)) + 1 / (2 * Q) = 1 / Q := by field_simp; ring
    rw [hswap] at hsum
    linarith
  have hrr0 : (0 : ℝ) < (r : ℝ) * r' := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
    positivity
  have : 1 / (Q : ℝ) ≤ 1 / ((r : ℝ) * r') := by
    apply one_div_le_one_div_of_le hrr0
    linarith
  linarith

/-- **Coprime fractions with the same value have the same denominator.** -/
lemma den_eq_of_coprime {r r' s s' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    (hc : Nat.Coprime s r) (hc' : Nat.Coprime s' r')
    (h : (s : ℝ) / r = (s' : ℝ) / r') : r = r' := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0' : (0 : ℝ) < r' := by exact_mod_cast hr'
  have hmul : (s : ℝ) * r' = (s' : ℝ) * r := by
    field_simp at h
    linarith
  have hnat : s * r' = s' * r := by exact_mod_cast hmul
  have hdvd : r ∣ r' := by
    have : r ∣ s * r' := ⟨s', by rw [hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc) this)
  have hdvd' : r' ∣ r := by
    have : r' ∣ s' * r := ⟨s, by rw [← hnat]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hc') this)
  exact Nat.dvd_antisymm hdvd hdvd'

/-- **Shor's period finding.**

Let `a` be a unit modulo `N` and let `r = orderOf a` be the (multiplicative) order of `a`,
i.e. the period of the modular exponentiation function `x ↦ a ^ x mod N`.
Suppose the quantum phase-estimation register has size `Q ≥ N ^ 2`, and the measured
outcome `c` yields a good estimate of some phase `s / r` (with `s` coprime to `r`),
namely `|c/Q - s/r| < 1/(2Q)` — the event which occurs with high probability.

Then:
1. `r` is a period of the modular exponentiation function;
2. `r` is the *least* positive period;
3. the classical post-processing is unambiguous: *any* fraction `s'/r'` in lowest terms
   with denominator `r' ≤ N` that is compatible with the measurement `c` has `r' = r`,
   so the algorithm outputs exactly the period `r`.
-/
theorem shor_period {N : ℕ} (hN : 1 < N) (a : (ZMod N)ˣ) (Q c s : ℕ)
    (hQ : ((N : ℝ)) ^ 2 ≤ Q) (r : ℕ) (hr : r = orderOf a) (hrN : r ≤ N)
    (hcop : Nat.Coprime s r)
    (hmeas : |(c : ℝ) / Q - (s : ℝ) / r| < 1 / (2 * Q)) :
    (∀ x : ℕ, ((a : ZMod N)) ^ (x + r) = ((a : ZMod N)) ^ x) ∧
    (∀ p : ℕ, 0 < p → (∀ x : ℕ, ((a : ZMod N)) ^ (x + p) = ((a : ZMod N)) ^ x) → r ≤ p) ∧
    (∀ s' r' : ℕ, 0 < r' → r' ≤ N → Nat.Coprime s' r' →
      |(c : ℝ) / Q - (s' : ℝ) / r'| < 1 / (2 * Q) → r' = r) := by
  haveI : NeZero N := ⟨by omega⟩
  have hrpos : 0 < r := by
    rw [hr]; exact orderOf_pos a
  have hQ0 : 0 < Q := by
    by_contra h
    push_neg at h
    interval_cases Q
    · have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      simp at hQ
      nlinarith
  have hpow : (a : (ZMod N)ˣ) ^ r = 1 := by
    rw [hr]; exact pow_orderOf_eq_one a
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have : ((a : ZMod N)) ^ r = 1 := by
      have := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hpow
      simpa using this
    rw [pow_add, this, mul_one]
  · intro p hp hper
    have h0 := hper 0
    simp only [zero_add, pow_zero] at h0
    have hu : (a : (ZMod N)ˣ) ^ p = 1 := by
      ext
      push_cast
      simpa using h0
    have : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hu
    rw [hr]
    exact Nat.le_of_dvd hp this
  · intro s' r' hr' hr'N hcop' hmeas'
    have := frac_unique hrpos hr' hrN hr'N hQ hQ0 hmeas hmeas'
    exact (den_eq_of_coprime hrpos hr' hcop hcop' this).symm

/-- **Non-vacuity witness.** The hypotheses of `QI.shor_period` are satisfiable:
take `N = 3`, `a = -1` (of order `r = 2` modulo `3`), register size `Q = 16 ≥ 3 ^ 2`,
measurement outcome `c = 8` and phase numerator `s = 1`. -/
theorem shor_period_nonvacuous :
    (∀ x : ℕ, ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ (x + 2) = ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ x) ∧
    (∀ p : ℕ, 0 < p →
        (∀ x : ℕ, ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ (x + p) = ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ x) →
        2 ≤ p) ∧
    (∀ s' r' : ℕ, 0 < r' → r' ≤ 3 → Nat.Coprime s' r' →
      |((8 : ℕ) : ℝ) / ((16 : ℕ) : ℝ) - (s' : ℝ) / r'| < 1 / (2 * ((16 : ℕ) : ℝ)) → r' = 2) := by
  have h2 : orderOf (-1 : (ZMod 3)ˣ) = 2 := by
    apply orderOf_eq_prime <;> decide
  exact shor_period (N := 3) (by norm_num) (-1) 16 8 1 (by norm_num) 2 h2.symm (by norm_num)
    (by norm_num) (by norm_num)

end QI

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

