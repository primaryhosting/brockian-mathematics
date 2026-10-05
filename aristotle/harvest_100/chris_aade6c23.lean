/-
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-!
## Setting

We formalise the quantitative core of the fault-tolerance threshold theorem for
concatenated quantum error-correcting codes.

A fault-tolerance scheme is described by two constants:

* a *threshold constant* `c > 0`, coming from the combinatorics of the fault-tolerant
  gadget: a level-`(L+1)` gadget fails only if at least two of the level-`L` gadgets it is
  built from fail, which gives the error recursion `p_{L+1} = c * p_L ^ 2`;
* a *gadget size* `d`, the number of level-`L` gadgets used to build one level-`(L+1)`
  gadget, so that one logical operation at concatenation level `L` costs `d ^ L` physical
  operations.

Solving the recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2` gives the closed form
`p_L = (c * p) ^ (2 ^ L) / c`, which is taken as the definition below and shown to satisfy
the recursion.

The threshold is `p_th = 1 / c`: for any physical error rate `p < p_th` the logical error
rate `p_L` tends to `0` doubly exponentially fast in the number of levels, so an arbitrary
target accuracy `ε` is reached at some finite level, and the physical overhead `d ^ L`
needed is only polylogarithmic in `1 / ε`.
-/

/-- The logical error rate after `L` levels of code concatenation, for a fault-tolerance
scheme with threshold constant `c` and physical error rate `p`.  This is the solution of
the error recursion `p_0 = p`, `p_{L+1} = c * p_L ^ 2`. -/
noncomputable def errorAtLevel (c p : ℝ) (L : ℕ) : ℝ := (c * p) ^ (2 ^ L) / c

/-- At level `0` the logical error rate is the physical error rate. -/
lemma errorAtLevel_zero {c : ℝ} (hc : c ≠ 0) (p : ℝ) : errorAtLevel c p 0 = p := by
  unfold errorAtLevel
  rw [pow_zero, pow_one, mul_comm, mul_div_assoc, div_self hc, mul_one]

/-- The concatenation recursion: two independent level-`L` failures are needed for a
level-`(L+1)` failure, up to the combinatorial constant `c`. -/
lemma errorAtLevel_succ {c : ℝ} (hc : c ≠ 0) (p : ℝ) (L : ℕ) :
    errorAtLevel c p (L + 1) = c * (errorAtLevel c p L) ^ 2 := by
  unfold errorAtLevel
  rw [pow_succ, pow_mul]
  field_simp

/-- Every nonnegative real is strictly below a power of two which is at most `2 * t + 2`. -/
lemma exists_pow_two_gt (t : ℝ) (ht : 0 ≤ t) :
    ∃ L : ℕ, t < (2 : ℝ) ^ L ∧ (2 : ℝ) ^ L ≤ 2 * t + 2 := by
  set n : ℕ := ⌊t⌋₊ + 1 with hn
  have hn1 : 1 ≤ n := Nat.le_add_left 1 _
  refine ⟨Nat.clog 2 n, ?_, ?_⟩
  · have h1 : t < (n : ℝ) := by
      have := Nat.lt_floor_add_one t
      simpa [hn] using this
    have h2 : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by
      have := Nat.le_pow_clog (b := 2) (by norm_num) n
      exact_mod_cast this
    linarith
  · rcases eq_or_lt_of_le hn1 with h | h
    · -- `n = 1`, so `Nat.clog 2 n = 0`
      have hzero : Nat.clog 2 n = 0 := by rw [← h]; simp
      rw [hzero, pow_zero]
      linarith
    · have hlt : 2 ^ (Nat.clog 2 n).pred < n :=
        Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
      have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) h
      have hsucc : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n := Nat.succ_pred_eq_of_pos hpos
      have hsplit : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n).pred * 2 := by
        conv_lhs => rw [← hsucc]
        rw [pow_succ]
      have hnat : 2 ^ Nat.clog 2 n ≤ 2 * n := by omega
      have hcast : (2 : ℝ) ^ Nat.clog 2 n ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
      have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
      have hnr : ((n : ℕ) : ℝ) = (⌊t⌋₊ : ℝ) + 1 := by push_cast [hn]; ring
      rw [hnr] at hcast
      linarith

/-- The key estimate: if `2 ^ L` exceeds `log (1 / (c ε)) / log (1 / (c p))` then the
level-`L` logical error rate is below `ε`. -/
lemma errorAtLevel_lt_of_lt {c p ε : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) (hcp : c * p < 1)
    (hε : 0 < ε) (L : ℕ)
    (hL : max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p)) < (2 : ℝ) ^ L) :
    errorAtLevel c p L < ε := by
  set q : ℝ := c * p with hq
  have hq0 : 0 ≤ q := mul_nonneg hc.le hp0
  rcases eq_or_lt_of_le hq0 with hq0' | hqpos
  · -- `p = 0`: the logical error rate vanishes identically
    have hzero : errorAtLevel c p L = 0 := by
      unfold errorAtLevel
      rw [← hq, ← hq0', zero_pow (Nat.two_pow_pos L).ne', zero_div]
    rw [hzero]; exact hε
  · -- `0 < c p < 1`
    have ha : 0 < Real.log (1 / q) := by
      rw [Real.lt_log_iff_exp_lt (by positivity), Real.exp_zero, lt_div_iff₀ hqpos]
      linarith
    set N : ℕ := 2 ^ L with hN
    have hcast : ((N : ℕ) : ℝ) = (2 : ℝ) ^ L := by push_cast [hN]; ring
    have hkey : max 0 (Real.log (1 / (c * ε))) < (N : ℝ) * Real.log (1 / q) := by
      rw [hcast]
      exact (div_lt_iff₀ ha).mp hL
    have hlogq : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
    have hlogce : Real.log (1 / (c * ε)) = -Real.log (c * ε) := by rw [one_div, Real.log_inv]
    rw [hlogq, hlogce] at hkey
    have hle : -Real.log (c * ε) ≤ max 0 (-Real.log (c * ε)) := le_max_right _ _
    have hlt : Real.log (q ^ N) < Real.log (c * ε) := by
      rw [Real.log_pow]
      linarith
    have hqN : q ^ N < c * ε :=
      (Real.log_lt_log_iff (pow_pos hqpos N) (by positivity)).mp hlt
    unfold errorAtLevel
    rw [← hq, ← hN, div_lt_iff₀ hc]
    linarith

/-- Below threshold, any target logical accuracy `ε` is achieved at some concatenation level
`L`, whose size is controlled: `2 ^ L ≤ 2 + 2 log(1/(cε)) / log(1/(cp))`. -/
lemma exists_level {c p ε : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) (hcp : c * p < 1) (hε : 0 < ε) :
    ∃ L : ℕ, errorAtLevel c p L < ε ∧
      (2 : ℝ) ^ L ≤ 2 + 2 * (max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p))) := by
  set t : ℝ := max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p)) with ht
  have ht0 : 0 ≤ t := by
    rcases le_or_gt (Real.log (1 / (c * p))) 0 with h | h
    · rcases eq_or_lt_of_le h with h' | h'
      · rw [ht, h', div_zero]
      · -- `log (1/(cp)) < 0` would force `c * p > 1`, contradicting `hcp`
        exfalso
        have hp0' : 0 ≤ c * p := mul_nonneg hc.le hp0
        rcases eq_or_lt_of_le hp0' with h0 | h0
        · rw [← h0] at h'; simp at h'
        · have h1 : (1 : ℝ) < 1 / (c * p) := by
            rw [lt_div_iff₀ h0]; linarith
          have := Real.log_pos h1
          linarith
    · exact div_nonneg (le_max_left _ _) h.le
  obtain ⟨L, hL1, hL2⟩ := exists_pow_two_gt t ht0
  exact ⟨L, errorAtLevel_lt_of_lt hc hp0 hcp hε L hL1, by linarith⟩

/-- Below threshold the logical error rate tends to `0` as the number of concatenation
levels grows. -/
lemma tendsto_errorAtLevel {c p : ℝ} (hc : 0 < c) (hp0 : 0 ≤ p) (hcp : c * p < 1) :
    Filter.Tendsto (fun L : ℕ => errorAtLevel c p L) Filter.atTop (nhds 0) := by
  have hq0 : 0 ≤ c * p := mul_nonneg hc.le hp0
  have hmain : Filter.Tendsto (fun L : ℕ => (c * p) ^ L / c) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hcp).div_const c
  refine squeeze_zero (fun L => ?_) (fun L => ?_) hmain
  · unfold errorAtLevel
    positivity
  · unfold errorAtLevel
    have hle : (c * p) ^ (2 ^ L) ≤ (c * p) ^ L :=
      pow_le_pow_of_le_one hq0 hcp.le (Nat.le_of_lt Nat.lt_two_pow_self)
    exact div_le_div_of_nonneg_right hle hc.le

/-- **Threshold theorem.**  For a fault-tolerance scheme with threshold constant `c > 0`
and gadget size `d ≤ 2 ^ k` there is a strictly positive error threshold `p_th = 1 / c`
such that for every physical error rate `p < p_th`:

* the logical error rates `errorAtLevel c p L` obey the concatenation recursion
  `p_0 = p`, `p_{L+1} = c * p_L ^ 2`;
* they tend to `0` as the number `L` of concatenation levels grows;
* consequently every target accuracy `ε > 0` is reached at some finite level `L`, and the
  physical overhead `d ^ L` of one logical operation is bounded by a fixed power of
  `2 + 2 log(1/(cε)) / log(1/(cp))`, i.e. it is polylogarithmic in `1/ε`.

Thus, below the constant error threshold, arbitrarily accurate fault-tolerant quantum
computation is possible with only polylogarithmic overhead. -/
theorem threshold_theorem (c : ℝ) (hc : 0 < c) (d k : ℕ) (hd : (d : ℝ) ≤ 2 ^ k) :
    ∃ pth : ℝ, 0 < pth ∧ ∀ p : ℝ, 0 ≤ p → p < pth →
      errorAtLevel c p 0 = p ∧
      (∀ L : ℕ, errorAtLevel c p (L + 1) = c * errorAtLevel c p L ^ 2) ∧
      Filter.Tendsto (fun L : ℕ => errorAtLevel c p L) Filter.atTop (nhds 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, errorAtLevel c p L < ε ∧
        (d : ℝ) ^ L ≤
          (2 + 2 * (max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p)))) ^ k := by
  refine ⟨1 / c, by positivity, fun p hp0 hp => ?_⟩
  have hcp : c * p < 1 := by
    rw [lt_div_iff₀ hc] at hp
    linarith
  refine ⟨errorAtLevel_zero hc.ne' p, fun L => errorAtLevel_succ hc.ne' p L,
    tendsto_errorAtLevel hc hp0 hcp, fun ε hε => ?_⟩
  obtain ⟨L, hlt, hbound⟩ := exists_level hc hp0 hcp hε
  refine ⟨L, hlt, ?_⟩
  set B : ℝ := 2 + 2 * (max 0 (Real.log (1 / (c * ε))) / Real.log (1 / (c * p))) with hB
  calc (d : ℝ) ^ L ≤ ((2 : ℝ) ^ k) ^ L := pow_le_pow_left₀ (by positivity) hd L
    _ = ((2 : ℝ) ^ L) ^ k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ B ^ k := pow_le_pow_left₀ (by positivity) hbound k

end QI

