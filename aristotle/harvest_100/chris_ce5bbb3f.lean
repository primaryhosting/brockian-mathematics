/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Filter Topology

namespace Math

/-- Every nonzero complex number has an `n`-th root for `n > 0`
(elementary consequence of the surjectivity of `Complex.exp` onto `ℂ \ {0}`). -/
theorem exists_pow_eq_of_ne_zero {z : ℂ} (hz : z ≠ 0) {n : ℕ} (hn : 0 < n) :
    ∃ u : ℂ, u ^ n = z := by
  refine ⟨Complex.exp (Complex.log z / n), ?_⟩
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), Complex.exp_log hz]

/-- Key step of the d'Alembert–Argand argument: if `t(0) ≠ 0` and `k > 0`, then the value `1`
of the function `w ↦ 1 + wᵏ t(w)` at `w = 0` is not a local minimum of its modulus. -/
theorem exists_norm_one_add_pow_mul_lt (t : ℂ[X]) {k : ℕ} (hk : 0 < k) (hc : t.eval 0 ≠ 0) :
    ∃ w : ℂ, ‖1 + w ^ k * t.eval w‖ < 1 := by
  set c : ℂ := t.eval 0 with hcdef
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u ^ k = -c⁻¹ :=
    exists_pow_eq_of_ne_zero (by simpa using hc) hk
  -- the auxiliary continuous function
  set f : ℝ → ℂ := fun e => t.eval ((e : ℂ) * u) / c with hf
  have hfcont : Continuous f := by
    fun_prop
  have hf0 : f 0 = 1 := by
    have h0u : ((0 : ℝ) : ℂ) * u = 0 := by simp
    simp only [hf, h0u, ← hcdef, div_self hc]
  have : ∀ᶠ e in 𝓝 (0 : ℝ), ‖f e - 1‖ < 1 / 2 := by
    have := hfcont.continuousAt (x := (0 : ℝ))
    rw [Metric.continuousAt_iff] at this
    obtain ⟨δ, hδ, hball⟩ := this (1 / 2) (by norm_num)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with e he
    have := hball he
    rwa [hf0, Complex.dist_eq] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 this
  refine ⟨(min (δ / 2) (1 / 2) : ℝ) * u, ?_⟩
  set e : ℝ := min (δ / 2) (1 / 2) with hedef
  have he0 : 0 < e := lt_min (by linarith) (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have hedist : dist e 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hfe : ‖f e - 1‖ < 1 / 2 := hball hedist
  have hek : (0:ℝ) < e ^ k := pow_pos he0 k
  have hek1 : (e : ℝ) ^ k ≤ 1 := pow_le_one₀ he0.le (by linarith)
  have key : 1 + ((e : ℂ) * u) ^ k * t.eval ((e : ℂ) * u)
      = (1 - (e : ℂ) ^ k) + (e : ℂ) ^ k * (1 - f e) := by
    have : ((e : ℂ) * u) ^ k = (e : ℂ) ^ k * (-c⁻¹) := by rw [mul_pow, hu]
    rw [this, hf]
    field_simp
    ring
  rw [key]
  calc ‖(1 - (e : ℂ) ^ k) + (e : ℂ) ^ k * (1 - f e)‖
      ≤ ‖(1 : ℂ) - (e : ℂ) ^ k‖ + ‖(e : ℂ) ^ k * (1 - f e)‖ := norm_add_le _ _
    _ = (1 - e ^ k) + e ^ k * ‖f e - 1‖ := by
        have h1 : ‖(1 : ℂ) - (e : ℂ) ^ k‖ = 1 - e ^ k := by
          rw [show ((1 : ℂ) - (e : ℂ) ^ k) = ((1 - e ^ k : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h2 : ‖((e : ℂ)) ^ k‖ = e ^ k := by
          rw [show ((e : ℂ) ^ k) = ((e ^ k : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg hek.le]
        rw [norm_mul, h1, h2, norm_sub_rev (1 : ℂ)]
    _ < (1 - e ^ k) + e ^ k * (1 / 2) := by
        have := mul_lt_mul_of_pos_left hfe hek
        linarith
    _ < 1 := by nlinarith

/-- d'Alembert's lemma: if a nonconstant complex polynomial does not vanish at a point,
then it takes a strictly smaller modulus somewhere else. -/
theorem exists_norm_eval_lt {p : ℂ[X]} (hp : 0 < p.degree) {z₀ : ℂ} (h0 : p.eval z₀ ≠ 0) :
    ∃ z : ℂ, ‖p.eval z‖ < ‖p.eval z₀‖ := by
  -- translate to `z₀ = 0`
  set r : ℂ[X] := p.comp (X + C z₀) with hr
  have hreval : ∀ w : ℂ, r.eval w = p.eval (w + z₀) := by
    intro w; simp [hr, eval_comp]
  have hr0 : r.eval 0 ≠ 0 := by simpa using (hreval 0).symm ▸ (by simpa using h0)
  have hrdeg : 0 < r.degree := by
    have h1 : (X + C z₀ : ℂ[X]).natDegree = 1 := by
      simp
    have : r.natDegree = p.natDegree := by
      rw [hr, natDegree_comp, h1, mul_one]
    have hpn : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 hp
    rw [← natDegree_pos_iff_degree_pos, this]
    exact hpn
  set a : ℂ := r.eval 0 with ha
  -- write `r = a * (1 + Xᵏ * t)` with `t(0) ≠ 0`
  set s : ℂ[X] := C a⁻¹ * r - 1 with hs
  have hs0 : s.eval 0 = 0 := by simp [hs, ← ha, inv_mul_cancel₀ hr0]
  have hsne : s ≠ 0 := by
    intro h
    have : C a⁻¹ * r = 1 := by
      have := h
      rw [hs, sub_eq_zero] at this
      exact this
    have hdeg : (C a⁻¹ * r).degree = 0 := by rw [this]; simp
    rw [degree_C_mul (by simpa using inv_ne_zero hr0)] at hdeg
    rw [hdeg] at hrdeg
    exact lt_irrefl _ hrdeg
  set k : ℕ := s.rootMultiplicity 0 with hk
  have hkpos : 0 < k := (rootMultiplicity_pos hsne).2 (by simpa [IsRoot] using hs0)
  set t : ℂ[X] := s /ₘ (X - C 0) ^ k with ht
  have hfact : (X : ℂ[X]) ^ k * t = s := by
    have := pow_mul_divByMonic_rootMultiplicity_eq s (0 : ℂ)
    simpa [ht, hk] using this
  have htc : t.eval 0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero (0 : ℂ) hsne
  obtain ⟨w, hw⟩ := exists_norm_one_add_pow_mul_lt t hkpos htc
  refine ⟨w + z₀, ?_⟩
  have hrw : r.eval w = a * (1 + w ^ k * t.eval w) := by
    have : r = C a * (1 + X ^ k * t) := by
      rw [hfact, hs, show (1 : ℂ[X]) + (C a⁻¹ * r - 1) = C a⁻¹ * r from by ring,
        ← mul_assoc, ← C_mul, mul_inv_cancel₀ hr0, C_1, one_mul]
    calc r.eval w = (C a * (1 + X ^ k * t)).eval w := by rw [← this]
      _ = a * (1 + w ^ k * t.eval w) := by simp
  have hane : ‖a‖ ≠ 0 := by simpa using hr0
  have : ‖r.eval w‖ < ‖a‖ := by
    rw [hrw, norm_mul]
    calc ‖a‖ * ‖1 + w ^ k * t.eval w‖ < ‖a‖ * 1 := by
          exact mul_lt_mul_of_pos_left hw (lt_of_le_of_ne (norm_nonneg a) (Ne.symm hane))
      _ = ‖a‖ := mul_one _
  rw [hreval w] at this
  simpa [ha, hreval 0] using this

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root. -/
theorem fta_algebra {p : ℂ[X]} (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 := by
  -- `‖p‖` attains a global minimum, and by d'Alembert's lemma the minimum value must be `0`
  have hcont : Continuous fun z : ℂ => ‖p.eval z‖ := p.continuous.norm
  have hlim : Tendsto (fun z : ℂ => ‖p.eval z‖) (cocompact ℂ) atTop := by
    refine Polynomial.tendsto_norm_atTop p hp ?_
    simpa [Metric.cobounded_eq_cocompact (α := ℂ)] using
      (tendsto_norm_cobounded_atTop (E := ℂ))
  obtain ⟨z₀, hz₀⟩ := hcont.exists_forall_le hlim
  refine ⟨z₀, ?_⟩
  by_contra h
  obtain ⟨z, hz⟩ := exists_norm_eval_lt hp h
  exact absurd (hz₀ z) (not_le.2 hz)

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

