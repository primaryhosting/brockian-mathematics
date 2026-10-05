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
theorem exists_pow_eq (a : ℂ) {n : ℕ} (hn : n ≠ 0) : ∃ w : ℂ, w ^ n = a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by simp [hn]⟩
  · refine ⟨Complex.exp (Complex.log a / n), ?_⟩
    rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), Complex.exp_log ha]

/-- A nonconstant polynomial can be written as `q = C (q.eval 0) + X ^ k * r` where `k ≥ 1`
and `r.eval 0 ≠ 0`. -/
theorem exists_lowest_term (q : ℂ[X]) (hq : 0 < q.natDegree) :
    ∃ (k : ℕ) (r : ℂ[X]), 0 < k ∧ r.eval 0 ≠ 0 ∧ q = C (q.eval 0) + X ^ k * r := by
  classical
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have hlead : q.coeff q.natDegree ≠ 0 := fun h => hq0 (leadingCoeff_eq_zero.mp h)
  have hex : ∃ n, 0 < n ∧ q.coeff n ≠ 0 := ⟨q.natDegree, hq, hlead⟩
  obtain ⟨hk0, hkne⟩ : 0 < Nat.find hex ∧ q.coeff (Nat.find hex) ≠ 0 := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hmin : ∀ d, 0 < d → d < k → q.coeff d = 0 := by
    intro d hd0 hd
    by_contra hc
    exact absurd (Nat.find_le ⟨hd0, hc⟩) (not_le.mpr hd)
  have hdvd : (X : ℂ[X]) ^ k ∣ (q - C (q.eval 0)) := by
    rw [X_pow_dvd_iff]
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp [coeff_zero_eq_eval_zero]
    · simp only [coeff_sub, coeff_C, if_neg (by omega : ¬ d = 0), sub_zero, hmin d hd0 hd]
  obtain ⟨r, hr⟩ := hdvd
  have hcoef : r.coeff 0 = q.coeff k := by
    have h2 := congrArg (fun f => Polynomial.coeff f k) hr
    simp only [coeff_sub, coeff_C, if_neg (by omega : ¬ k = 0), sub_zero] at h2
    have h3 : (X ^ k * r).coeff k = r.coeff 0 := by simpa using coeff_X_pow_mul r k 0
    rw [h3] at h2
    exact h2.symm
  refine ⟨k, r, hk0, ?_, by linear_combination (norm := ring_nf) hr⟩
  rw [← coeff_zero_eq_eval_zero, hcoef]
  exact hkne

/-- d'Alembert's lemma at the origin: if `q` is nonconstant and `q.eval 0 ≠ 0`, then `‖q.eval ·‖`
takes a strictly smaller value somewhere. -/
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
theorem exists_norm_lt (p : ℂ[X]) (hp : 0 < p.natDegree) (z₀ : ℂ) (h : p.eval z₀ ≠ 0) :
    ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z₀‖ := by
  set q := p.comp (X + C z₀) with hq
  have hev : ∀ z : ℂ, q.eval z = p.eval (z + z₀) := by
    intro z; simp [hq, eval_comp]
  have hdeg : 0 < q.natDegree := by
    rw [hq, natDegree_comp]; simpa using hp
  have h0 : q.eval 0 ≠ 0 := by rw [hev]; simpa using h
  obtain ⟨z, hz⟩ := exists_norm_lt_zero q hdeg h0
  rw [hev, hev] at hz
  exact ⟨z + z₀, by simpa using hz⟩

end FTA

namespace Math

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root. -/
theorem fta_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 := by
  obtain ⟨x₀, hx₀⟩ := p.exists_forall_norm_le
  refine ⟨x₀, ?_⟩
  by_contra h
  have hnat : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hp
  obtain ⟨z, hz⟩ := FTA.exists_norm_lt p hnat x₀ h
  exact absurd (hx₀ z) (not_le.mpr hz)

end Math

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

