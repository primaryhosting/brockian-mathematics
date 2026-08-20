import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem caseB_real {x y s m : ℝ} (hx : 20000 ≤ x) (hy : 2 * x + 1 ≤ y) (hy2 : y ^ 2 ≤ x ^ 3)
    (hs : s ^ 2 ≤ y) (hm0 : 0 ≤ m) (hm1 : m ≤ x) (hm3 : 3 * m ≤ y) :
    Real.log x + x * Real.log (2 * x) + s * Real.log y + m * Real.log 4
      ≤ x * Real.log 4 + x * Real.log y := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  -- the fourth root of `x`
  obtain ⟨v, hv0, hv4⟩ : ∃ v : ℝ, 0 < v ∧ v ^ 4 = x := by
    refine ⟨Real.sqrt (Real.sqrt x), Real.sqrt_pos.2 (Real.sqrt_pos.2 hx0), ?_⟩
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have h2 : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
    calc (Real.sqrt (Real.sqrt x)) ^ 4 = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [h2]
      _ = x := h1
  have hv : 11.8 ≤ v := by
    by_contra hc
    rw [not_le] at hc
    have h4 : v ^ 4 < (11.8 : ℝ) ^ 4 := by gcongr
    rw [hv4] at h4
    norm_num at h4
    linarith
  -- the square root of `y`
  obtain ⟨w, hw0, hw2⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ^ 2 = y :=
    ⟨Real.sqrt y, Real.sqrt_nonneg y, Real.sq_sqrt hy0.le⟩
  have hsw : s ≤ w := by nlinarith [hs, hw0, hw2]
  -- logarithm bounds
  have hlogx_up : Real.log x ≤ 7.1 + v / 4 := by rw [← hv4]; exact log_pow4_le hv0
  have hlogx_lo : (9 : ℝ) ≤ Real.log x := nine_le_log hx
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlog4 : m * Real.log 4 ≤ 1.3863 * m := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h2 : Real.log 4 ≤ 1.3863 := by rw [h]; linarith [log_two_le]
    calc m * Real.log 4 ≤ m * 1.3863 := mul_le_mul_of_nonneg_left h2 hm0
      _ = 1.3863 * m := by ring
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul two_ne_zero hx0.ne'
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- it suffices to prove the following inequality
  have key : Real.log x + s * Real.log y + m * Real.log 4
      ≤ x * (Real.log 2 + Real.log y - Real.log x) := by
    have hsy : s * Real.log y ≤ w * Real.log y := mul_le_mul_of_nonneg_right hsw hlogy0
    rcases le_or_gt y (3 * x) with hcase | hcase
    · -- `y ≤ 3 * x`, use `m ≤ y / 3`
      have hlogy_up : Real.log y ≤ 8.5 + v / 4 := by
        have h1 : Real.log y ≤ Real.log (3 * x) := Real.log_le_log hy0 hcase
        have h2 : Real.log (3 * x) = Real.log 3 + Real.log x :=
          Real.log_mul (by norm_num) hx0.ne'
        have h3 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        linarith [log_two_le]
      have hwy : w * Real.log y ≤ w * (8.5 + v / 4) := mul_le_mul_of_nonneg_left hlogy_up hw0
      have hpoly := polyP1 hv hw0 (by rw [hw2, hv4]; linarith)
      rw [hv4] at hpoly
      have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 0.23 * x + 1.3863 * m := by
        linarith
      -- lower bound for the right-hand side
      rcases le_or_gt (3 * y) (7 * x) with hc1 | hc1
      · have hd : (1.3862471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (2 * x) ≤ Real.log y := Real.log_le_log (by linarith) (by linarith)
          rw [hlog2x] at h1
          linarith [log_two_ge]
        have hR : x * 1.3862471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * (7 * x / 9) := by
          have : m ≤ 7 * x / 9 := by linarith
          linarith
        linarith
      · rcases le_or_gt (3 * y) (8 * x) with hc2 | hc2
        · have hd : (1.5291471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
            have h1 : Real.log (7 / 3 * x) ≤ Real.log y :=
              Real.log_le_log (by positivity) (by linarith)
            rw [Real.log_mul (by norm_num) hx0.ne'] at h1
            linarith [log_two_ge, log_seven_thirds_ge]
          have hR : x * 1.5291471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
            mul_le_mul_of_nonneg_left hd hx0.le
          have hmx : 1.3863 * m ≤ 1.3863 * (8 * x / 9) := by
            have : m ≤ 8 * x / 9 := by linarith
            linarith
          linarith
        · have hd : (1.6361471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
            have h1 : Real.log (8 / 3 * x) ≤ Real.log y :=
              Real.log_le_log (by positivity) (by linarith)
            rw [Real.log_mul (by norm_num) hx0.ne'] at h1
            linarith [log_two_ge, log_eight_thirds_ge]
          have hR : x * 1.6361471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
            mul_le_mul_of_nonneg_left hd hx0.le
          have hmx : 1.3863 * m ≤ 1.3863 * x := by
            have : m ≤ x := by linarith
            linarith
          linarith
    · rcases le_or_gt y (9 * x) with hcase2 | hcase2
      · -- `3 * x ≤ y ≤ 9 * x`, use `m ≤ x`
        have hlogy_up : Real.log y ≤ 9.9 + v / 4 := by
          have h1 : Real.log y ≤ Real.log (9 * x) := Real.log_le_log hy0 hcase2
          have h2 : Real.log (9 * x) = Real.log 9 + Real.log x :=
            Real.log_mul (by norm_num) hx0.ne'
          linarith [log_nine_le]
        have hwy : w * Real.log y ≤ w * (9.9 + v / 4) := mul_le_mul_of_nonneg_left hlogy_up hw0
        have hpoly := polyP2 hv (by rw [hw2, hv4]; linarith)
        rw [hv4] at hpoly
        have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 0.3 * x + 1.3863 * m := by
          linarith
        have hd : (1.7191471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (3 * x) ≤ Real.log y := Real.log_le_log (by positivity) (by linarith)
          rw [Real.log_mul (by norm_num) hx0.ne'] at h1
          linarith [log_two_ge, log_three_ge]
        have hR : x * 1.7191471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * x := by linarith
        linarith
      · -- `9 * x ≤ y`, use `m ≤ x`
        have hlogy_up : Real.log y ≤ 10.65 + 0.375 * v := by
          have h1 : 2 * Real.log y ≤ 3 * Real.log x := by
            have h2 : Real.log (y ^ 2) ≤ Real.log (x ^ 3) := Real.log_le_log (by positivity) hy2
            rw [Real.log_pow, Real.log_pow] at h2; push_cast at h2; linarith
          linarith
        have hwy : w * Real.log y ≤ w * (10.65 + 0.375 * v) :=
          mul_le_mul_of_nonneg_left hlogy_up hw0
        have hwb : w ^ 2 ≤ v ^ 6 := by
          have h1 : (w ^ 2) ^ 2 ≤ (v ^ 6) ^ 2 := by
            rw [hw2, show (v ^ 6) ^ 2 = (v ^ 4) ^ 3 by ring, hv4]; exact hy2
          have h2 : (0 : ℝ) < v ^ 6 := by positivity
          nlinarith [h1, h2, sq_nonneg w, hw2, hy0]
        have hpoly := polyP34 hv hwb
        rw [hv4] at hpoly
        have hL : Real.log x + s * Real.log y + m * Real.log 4 ≤ 1.45 * x + 1.3863 * m := by
          linarith
        have hd : (2.8831471 : ℝ) ≤ Real.log 2 + Real.log y - Real.log x := by
          have h1 : Real.log (9 * x) ≤ Real.log y := Real.log_le_log (by positivity) (by linarith)
          rw [Real.log_mul (by norm_num) hx0.ne'] at h1
          linarith [log_two_ge, log_nine_ge]
        have hR : x * 2.8831471 ≤ x * (Real.log 2 + Real.log y - Real.log x) :=
          mul_le_mul_of_nonneg_left hd hx0.le
        have hmx : 1.3863 * m ≤ 1.3863 * x := by linarith
        linarith
  rw [hlog2x, hlog4eq]
  have expand : x * (Real.log 2 + Real.log y - Real.log x)
      = x * Real.log 2 + x * Real.log y - x * Real.log x := by ring
  rw [expand] at key
  rw [hlog4eq] at key
  linarith

