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
