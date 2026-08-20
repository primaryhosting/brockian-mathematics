import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem exists_absorbing_rotZ (D : Set E) (hD : D.Countable)
    (haxis : ∀ x ∈ D, ¬ (x 0 = 0 ∧ x 1 = 0)) :
    ∃ g : E ≃ₗᵢ[ℝ] E, ∀ n : ℕ, 0 < n → Disjoint ((g ^ n) • D) D := by
  classical
  -- the set of "bad" angles
  set Bad : Set ℝ := ⋃ n ∈ {n : ℕ | 0 < n}, ⋃ x ∈ D, ⋃ y ∈ D,
    {t : ℝ | Real.cos ((n : ℝ) * t) * x 0 - Real.sin ((n : ℝ) * t) * x 1 = y 0 ∧
      Real.sin ((n : ℝ) * t) * x 0 + Real.cos ((n : ℝ) * t) * x 1 = y 1} with hBad
  have hBadCountable : Bad.Countable := by
    refine Set.Countable.biUnion (Set.to_countable _) fun n hn => ?_
    refine Set.Countable.biUnion hD fun x hx => ?_
    refine Set.Countable.biUnion hD fun y hy => ?_
    have hx2 : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
      intro h
      obtain ⟨h0, h1⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h
      exact haxis x hx ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0,
        pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1⟩
    set c₀ : ℝ := (x 0 * y 0 + x 1 * y 1) / (x 0 ^ 2 + x 1 ^ 2) with hc₀
    set s₀ : ℝ := (x 0 * y 1 - x 1 * y 0) / (x 0 ^ 2 + x 1 ^ 2) with hs₀
    have hsub : {t : ℝ | Real.cos ((n : ℝ) * t) * x 0 - Real.sin ((n : ℝ) * t) * x 1 = y 0 ∧
        Real.sin ((n : ℝ) * t) * x 0 + Real.cos ((n : ℝ) * t) * x 1 = y 1} ⊆
        {t : ℝ | (n : ℝ) * t ∈ {u : ℝ | Real.cos u = c₀ ∧ Real.sin u = s₀}} := by
      rintro t ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [hc₀, eq_div_iff hx2]
        linear_combination (x 0) * h1 + (x 1) * h2
      · rw [hs₀, eq_div_iff hx2]
        linear_combination (-(x 1)) * h1 + (x 0) * h2
    exact Set.Countable.mono hsub (countable_preimage_mul hn (countable_cos_sin_eq c₀ s₀))
  -- pick a good angle
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    exact Cardinal.not_countable_real (hBadCountable.mono fun x _ => hcon x)
  refine ⟨rotZ (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t), fun n hn => ?_⟩
  refine Set.disjoint_left.2 ?_
  rintro z ⟨x, hx, rfl⟩ hz
  refine ht ?_
  rw [hBad]
  refine Set.mem_biUnion (show n ∈ {n : ℕ | 0 < n} from hn) ?_
  refine Set.mem_biUnion hx ?_
  refine Set.mem_biUnion hz ?_
  have hpow : (rotZ (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t)) ^ n
      = rotZ (Real.cos ((n : ℝ) * t)) (Real.sin ((n : ℝ) * t)) (Real.cos_sq_add_sin_sq _) :=
    rotZ_pow t n _ _
  constructor
  · have := congrArg (fun v : E => v 0) (congrArg (fun (h : E ≃ₗᵢ[ℝ] E) => h x) hpow)
    simpa using this.symm
  · have := congrArg (fun v : E => v 1) (congrArg (fun (h : E ≃ₗᵢ[ℝ] E) => h x) hpow)
    simpa using this.symm

