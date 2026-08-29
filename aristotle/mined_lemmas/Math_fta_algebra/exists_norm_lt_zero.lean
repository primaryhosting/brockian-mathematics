/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The proof below is the classical d'Alembert–Argand ("minimum modulus") argument:

* `FTA.exists_pow_eq`: every complex number has `n`-th roots (via `exp`/`log`);
* `FTA.exists_lowest_term`: a nonconstant polynomial can be written `C (q.eval 0) + X ^ k * r`
  with `k ≥ 1` and `r.eval 0 ≠ 0`;
* `FTA.exists_norm_lt`: d'Alembert's lemma — at a point which is not a root, `‖p‖` is not
  minimal;
* `Math.fta_algebra`: since `‖p.eval ·‖` attains a global minimum (it tends to infinity at
  infinity), that minimum must be `0`.

It does not use `Complex.exists_root` or the `IsAlgClosed ℂ` instance from Mathlib.
-/

open Polynomial

namespace FTA

/-- Every complex number has an `n`-th root for `n ≠ 0`. -/

theorem exists_norm_lt_zero (q : ℂ[X]) (hq : 0 < q.natDegree) (h0 : q.eval 0 ≠ 0) :
    ∃ z : ℂ, ‖q.eval z‖ < ‖q.eval 0‖ := by
  obtain ⟨k, r, hk, hb, hqeq⟩ := exists_lowest_term q hq
  set a := q.eval 0 with ha
  set b := r.eval 0 with hbdef
  obtain ⟨w, hw⟩ := exists_pow_eq (-a / b) (n := k) (by omega)
  have hbw : b * w ^ k = -a := by rw [hw]; field_simp
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : k ≠ 0), mul_zero] at hbw
    exact h0 (neg_eq_zero.mp hbw.symm)
  have hna : (0:ℝ) < ‖a‖ := norm_pos_iff.mpr h0
  have hnw : (0:ℝ) < ‖w‖ ^ k := by positivity
  set ε : ℝ := ‖a‖ / (2 * ‖w‖ ^ k) with hε
  have hεpos : 0 < ε := by positivity
  have hcont : Continuous fun t : ℝ => r.eval ((t : ℂ) * w) := by fun_prop
  have htend : Filter.Tendsto (fun t : ℝ => r.eval ((t : ℂ) * w)) (nhds 0) (nhds b) := by
    have h := hcont.continuousAt (x := (0:ℝ))
    simp only [ContinuousAt, Complex.ofReal_zero, zero_mul] at h
    exact h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhds_nhds.mp htend ε hεpos
  set t : ℝ := min (δ / 2) (1 / 2) with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htδ : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    calc t ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have hsmall : ‖r.eval ((t : ℂ) * w) - b‖ < ε := by
    have := hδ' htδ
    rwa [Complex.dist_eq] at this
  refine ⟨(t : ℂ) * w, ?_⟩
  have heval : q.eval ((t:ℂ) * w) = a * (1 - (t:ℂ) ^ k)
      + (t:ℂ) ^ k * w ^ k * (r.eval ((t:ℂ) * w) - b) := by
    rw [hqeq]
    simp only [eval_add, eval_C, eval_mul, eval_pow, eval_X]
    rw [mul_pow]
    linear_combination ((t:ℂ) ^ k) * hbw
  have htk : (0:ℝ) < t ^ k := by positivity
  have htk1 : t ^ k ≤ 1 := pow_le_one₀ ht0.le (by linarith)
  have hnormt : ‖((t:ℂ)) ^ k‖ = t ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have e1 : ‖a * (1 - (t:ℂ) ^ k)‖ = ‖a‖ * (1 - t ^ k) := by
    rw [norm_mul, show ((1:ℂ) - (t:ℂ) ^ k) = ((1 - t ^ k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e2 : ‖(t:ℂ) ^ k * w ^ k * (r.eval ((t:ℂ) * w) - b)‖ ≤ t ^ k * ‖w‖ ^ k * ε := by
    rw [norm_mul, norm_mul, hnormt, norm_pow]
    exact mul_le_mul_of_nonneg_left hsmall.le (by positivity)
  have key : ‖q.eval ((t:ℂ) * w)‖ ≤ ‖a‖ * (1 - t ^ k) + t ^ k * ‖w‖ ^ k * ε := by
    rw [heval]
    exact (norm_add_le _ _).trans (add_le_add (le_of_eq e1) e2)
  have hfinal : ‖a‖ * (1 - t ^ k) + t ^ k * ‖w‖ ^ k * ε < ‖a‖ := by
    have hεeq : ‖w‖ ^ k * ε = ‖a‖ / 2 := by rw [hε]; field_simp
    calc ‖a‖ * (1 - t ^ k) + t ^ k * ‖w‖ ^ k * ε
        = ‖a‖ * (1 - t ^ k) + t ^ k * (‖w‖ ^ k * ε) := by ring
      _ = ‖a‖ - t ^ k * (‖a‖ / 2) := by rw [hεeq]; ring
      _ < ‖a‖ := by nlinarith
  exact lt_of_le_of_lt key hfinal

/-- d'Alembert's lemma: the modulus of a nonconstant complex polynomial has no global minimum at
a point which is not a root. -/
