import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

/-- The logical error rate of a fault-tolerant scheme built by `k`-fold concatenation of a
distance-3 (single-error-correcting) code, starting from physical error rate `p`.

One level of concatenation replaces each gate by a fault-tolerant gadget which fails only if at
least two of its constituent locations fail; with `C` the number of malignant pairs of locations
in a gadget, the standard level-reduction estimate gives
`p_{k+1} = C * p_k ^ 2`. -/

lemma exists_level (C p : ℝ) (hC : 0 < C) (hp : 0 ≤ p) (hlt : C * p < 1)
    (ε : ℝ) (hε : 0 < ε) (hεC : C * ε < 1) :
    ∃ k : ℕ, logicalErrorRate C p k < ε ∧
      (2 : ℝ) ^ k ≤ 2 * (Real.log (1 / (C * ε)) / Real.log (1 / (C * p)) + 1) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · -- `p = 0`: no errors at all, level `0` already works.
    refine ⟨0, ?_, ?_⟩
    · simpa [← hp0] using hε
    · have hb : 0 ≤ Real.log (1 / (C * ε)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hden : Real.log (1 / (C * p)) = 0 := by
        simp [← hp0]
      rw [hden]
      simp
  · -- `0 < p < 1 / C`.
    set r : ℝ := C * p with hr
    have hr0 : 0 < r := by positivity
    have ha : 0 < Real.log (1 / r) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hr0]
      linarith
    have hb : 0 ≤ Real.log (1 / (C * ε)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      linarith
    set a : ℝ := Real.log (1 / r) with hadef
    set b : ℝ := Real.log (1 / (C * ε)) with hbdef
    set T : ℝ := b / a with hT
    have hT0 : 0 ≤ T := div_nonneg hb ha.le
    have hex : ∃ k : ℕ, T < (2 : ℝ) ^ k := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (α := ℝ) T (by norm_num : (1:ℝ) < 2)
      exact ⟨k, hk⟩
    classical
    let k := Nat.find hex
    have hk : T < (2 : ℝ) ^ k := Nat.find_spec hex
    refine ⟨k, ?_, ?_⟩
    · -- accuracy
      have hlogr : Real.log r < 0 := by
        have : Real.log r = -a := by
          rw [hadef, one_div, Real.log_inv, neg_neg]
        rw [this]; linarith
      have hkey : Real.log (r ^ (2 ^ k)) < Real.log (C * ε) := by
        have h1 : Real.log (r ^ (2 ^ k)) = (2 ^ k : ℕ) * Real.log r := Real.log_pow _ _
        have h2 : Real.log (C * ε) = -b := by
          rw [hbdef, one_div, Real.log_inv, neg_neg]
        have h3 : b < (2 : ℝ) ^ k * a := by
          rw [hT] at hk
          rw [div_lt_iff₀ ha] at hk
          linarith
        have h4 : Real.log r = -a := by
          rw [hadef, one_div, Real.log_inv, neg_neg]
        rw [h1, h2, h4]
        push_cast
        linarith
      have hrk : r ^ (2 ^ k) < C * ε := by
        have := (Real.log_lt_log_iff (by positivity) (by positivity)).mp hkey
        exact this
      rw [logicalErrorRate_eq C p hC.ne' k, ← hr, div_lt_iff₀ hC]
      linarith [hrk]
    · -- overhead bound
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]
        simp only [pow_zero]
        linarith
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
        have hmin : ¬ (T < (2 : ℝ) ^ m) := by
          have : m < k := by omega
          exact Nat.find_min hex this
        push_neg at hmin
        rw [hm, pow_succ]
        nlinarith [hmin]

/-- **Threshold theorem for fault-tolerant quantum computation.**

For any fault-tolerant gadget constant `C > 0` there is a strictly positive error threshold
`p_th = 1 / C` with the following property.  Whenever the physical error rate `p` per location
is below the threshold, concatenated encoding yields a fault-tolerant simulation whose logical
error rate:

* is non-increasing in the number `k` of concatenation levels;
* tends to `0` as `k → ∞`;
* is below any prescribed target accuracy `ε` for some finite number `k` of levels, where the
  overhead factor `2 ^ k` (the number of physical locations per logical location, up to the
  constant size of one gadget) grows only linearly in
  `log (1 / (C * ε)) / log (1 / (C * p))`, i.e. polylogarithmically in `1 / ε`.

Thus arbitrarily long/accurate quantum computation is possible below the threshold, at
polylogarithmic overhead. -/
