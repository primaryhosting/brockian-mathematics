/-
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `errAfter C p L` is the logical error rate of a gate location after `L` levels of
code concatenation, in the standard fault-tolerance recursion: one level of encoding
turns a physical error rate `q` into a logical error rate `C * q ^ 2`, where `C` counts
the number of pairs of fault locations in one level-1 rectangle. -/
noncomputable def errAfter (C p : ℝ) : ℕ → ℝ
  | 0 => p
  | L + 1 => C * (errAfter C p L) ^ 2

@[simp] lemma errAfter_zero (C p : ℝ) : errAfter C p 0 = p := rfl

@[simp] lemma errAfter_succ (C p : ℝ) (L : ℕ) :
    errAfter C p (L + 1) = C * (errAfter C p L) ^ 2 := rfl

/-- Closed form of the concatenation recursion: after `L` levels the error rate is
`(1/C) * (C * p) ^ (2 ^ L)`, doubly exponentially small when `C * p < 1`. -/
lemma errAfter_closed_form {C : ℝ} (hC : 0 < C) (p : ℝ) (L : ℕ) :
    errAfter C p L = (1 / C) * (C * p) ^ (2 ^ L) := by
  induction L with
  | zero => simp; field_simp
  | succ L ih =>
      rw [errAfter_succ, ih]
      have h2 : (2 : ℕ) ^ (L + 1) = 2 ^ L * 2 := by ring
      rw [h2, pow_mul]
      field_simp

/-- The error rate stays nonnegative. -/
lemma errAfter_nonneg {C p : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (L : ℕ) : 0 ≤ errAfter C p L := by
  rw [errAfter_closed_form hC p L]
  positivity

/-- Below threshold the error rate is monotonically non-increasing in the concatenation level. -/
lemma errAfter_antitone {C p : ℝ} (hC : 0 < C) (hp : 0 ≤ p) (hlt : C * p ≤ 1)
    {L M : ℕ} (hLM : L ≤ M) : errAfter C p M ≤ errAfter C p L := by
  rw [errAfter_closed_form hC p L, errAfter_closed_form hC p M]
  have hCp : 0 ≤ C * p := by positivity
  have hpow : (C * p) ^ (2 ^ M) ≤ (C * p) ^ (2 ^ L) :=
    pow_le_pow_of_le_one hCp hlt (Nat.pow_le_pow_right (by norm_num) hLM)
  have : (0:ℝ) < 1 / C := by positivity
  exact mul_le_mul_of_nonneg_left hpow this.le

/-- Existence of a concatenation level whose (dyadic) size exceeds a given bound,
together with the doubling control on the least such level. -/
lemma exists_level {t : ℝ} (ht : 1 ≤ t) :
    ∃ L : ℕ, t ≤ 2 ^ L ∧ (2 : ℝ) ^ L ≤ 2 * t := by
  have hex : ∃ L : ℕ, t ≤ (2 : ℝ) ^ L := by
    obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (y := (2:ℝ)) t (by norm_num)
    exact ⟨L, hL.le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using by linarith
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ (t ≤ (2:ℝ) ^ m) := Nat.find_min hex (by omega)
    push_neg at hlt
    rw [hm, pow_succ]
    nlinarith

/-- **Quantitative threshold estimate.** Below threshold (`p < 1/C`), for every target
accuracy `ε ∈ (0,1]` there is a concatenation level `L` at which the logical error rate is
at most `ε`, while the resource overhead `d ^ L` (with `d` physical locations per block,
`d ≤ 2 ^ k`) grows only polylogarithmically in `1/ε`. -/
lemma exists_level_error_le_with_overhead {C : ℝ} (hC : 0 < C) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p < 1 / C) (d k : ℕ) (hd : (d : ℝ) ≤ 2 ^ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ L : ℕ,
      errAfter C p L ≤ ε ∧ (d : ℝ) ^ L ≤ K * (1 + Real.log (1 / ε)) ^ k := by
  have hq0 : 0 ≤ C * p := by positivity
  have hq1 : C * p < 1 := by
    have h := (lt_div_iff₀ hC).mp hp
    linarith [h]
  set δ : ℝ := max (C * p) (1 / 2) with hδdef
  have hδ0 : 0 < δ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hδ1 : δ < 1 := max_lt hq1 (by norm_num)
  have hqδ : C * p ≤ δ := le_max_left _ _
  set β : ℝ := -Real.log δ with hβdef
  have hβ : 0 < β := by
    have hlog := Real.log_neg hδ0 hδ1
    simp only [hβdef]
    linarith
  set A : ℝ := 1 + (1 + |Real.log C|) / β with hAdef
  have hA1 : 1 ≤ A := by
    have hnn : 0 ≤ (1 + |Real.log C|) / β := by positivity
    simp only [hAdef]
    linarith
  refine ⟨(2 * A) ^ k, by positivity, ?_⟩
  intro ε hε hε1
  have hu0 : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    linarith
  set u : ℝ := Real.log (1 / ε) with hudef
  have ht1 : 1 ≤ A * (1 + u) := by nlinarith
  obtain ⟨L, hLt, hL2⟩ := exists_level ht1
  have hn : A * (1 + u) ≤ ((2 ^ L : ℕ) : ℝ) := by push_cast; exact hLt
  refine ⟨L, ?_, ?_⟩
  · rw [errAfter_closed_form hC p L]
    have hpow : (C * p) ^ (2 ^ L) ≤ δ ^ (2 ^ L) := pow_le_pow_left₀ hq0 hqδ _
    have hkey : δ ^ (2 ^ L) ≤ C * ε := by
      have hpos : (0:ℝ) < δ ^ (2 ^ L) := by positivity
      have hCe : (0:ℝ) < C * ε := by positivity
      rw [← Real.log_le_log_iff hpos hCe, Real.log_pow,
        Real.log_mul (ne_of_gt hC) (ne_of_gt hε)]
      have hlogε : Real.log ε = -u := by
        simp [hudef]
      have hlogδ : Real.log δ = -β := by simp [hβdef]
      rw [hlogε, hlogδ]
      have habs : -Real.log C ≤ |Real.log C| := neg_le_abs _
      have hAβ : A * β = β + (1 + |Real.log C|) := by
        rw [hAdef]
        field_simp
      have h1 : A * (1 + u) * β ≤ ((2 ^ L : ℕ) : ℝ) * β :=
        mul_le_mul_of_nonneg_right hn hβ.le
      have h2 : A * (1 + u) * β = (1 + u) * (β + (1 + |Real.log C|)) := by
        rw [show A * (1 + u) * β = (1 + u) * (A * β) by ring, hAβ]
      nlinarith [habs, hu0, hβ.le, abs_nonneg (Real.log C)]
    have h1C : (0:ℝ) < 1 / C := by positivity
    calc (1 / C) * (C * p) ^ (2 ^ L) ≤ (1 / C) * (C * ε) :=
          mul_le_mul_of_nonneg_left (hpow.trans hkey) h1C.le
      _ = ε := by field_simp
  · have hdL : (d : ℝ) ^ L ≤ ((2 : ℝ) ^ k) ^ L := pow_le_pow_left₀ (by positivity) hd L
    have hswap : ((2 : ℝ) ^ k) ^ L = ((2 : ℝ) ^ L) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hmono : ((2 : ℝ) ^ L) ^ k ≤ (2 * (A * (1 + u))) ^ k :=
      pow_le_pow_left₀ (by positivity) hL2 k
    have hfac : (2 * (A * (1 + u))) ^ k = (2 * A) ^ k * (1 + u) ^ k := by
      rw [← mul_pow]; ring_nf
    calc (d : ℝ) ^ L ≤ ((2 : ℝ) ^ k) ^ L := hdL
      _ = ((2 : ℝ) ^ L) ^ k := hswap
      _ ≤ (2 * (A * (1 + u))) ^ k := hmono
      _ = (2 * A) ^ k * (1 + u) ^ k := hfac

/-- **Threshold theorem for fault-tolerant quantum computation.**

Model: one level of concatenated encoding maps a failure rate `q` of a gate location to a
logical failure rate `C * q ^ 2`, so after `L` levels of concatenation the logical failure
rate is `errAfter C p L`; a level-`L` block uses `d ^ L` physical locations, where
`d ≤ 2 ^ k`.

If the physical error rate `p` lies strictly below the constant threshold `p_th = 1 / C`,
then:

1. the level-`L` logical error rate equals `(1/C) * (C p) ^ (2 ^ L)`, i.e. it is suppressed
   doubly exponentially in the number of concatenation levels;
2. it is non-increasing in `L`, and any target accuracy `ε > 0` is achieved from some level
   onwards;
3. quantitatively, there is a constant `K` such that every target accuracy `ε ∈ (0,1]` is
   reached at a level `L` whose overhead `d ^ L` is at most `K * (1 + log (1/ε)) ^ k`, i.e.
   polylogarithmic in `1/ε`.

Hence below the threshold, arbitrarily accurate fault-tolerant quantum computation is
possible at only polylogarithmic overhead. -/
theorem threshold_theorem {C : ℝ} (hC : 0 < C) {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 1 / C)
    (d k : ℕ) (hd : (d : ℝ) ≤ 2 ^ k) :
    (∀ L : ℕ, errAfter C p L = (1 / C) * (C * p) ^ (2 ^ L)) ∧
    (∀ L M : ℕ, L ≤ M → errAfter C p M ≤ errAfter C p L) ∧
    (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → errAfter C p L < ε) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ L : ℕ,
        errAfter C p L ≤ ε ∧ (d : ℝ) ^ L ≤ K * (1 + Real.log (1 / ε)) ^ k) := by
  have hq1 : C * p < 1 := by
    have h := (lt_div_iff₀ hC).mp hp
    linarith [h]
  refine ⟨fun L => errAfter_closed_form hC p L,
    fun L M hLM => errAfter_antitone hC hp0 hq1.le hLM, ?_,
    exists_level_error_le_with_overhead hC hp0 hp d k hd⟩
  intro ε hε
  obtain ⟨K, -, hK⟩ := exists_level_error_le_with_overhead hC hp0 hp d k hd
  obtain ⟨L₀, hL₀, -⟩ := hK (min (ε / 2) 1) (by positivity) (min_le_right _ _)
  refine ⟨L₀, fun L hL => ?_⟩
  have hanti := errAfter_antitone hC hp0 hq1.le hL
  have hmin : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
  linarith

end QI

#print axioms QI.threshold_theorem

