import Mathlib
import Topology.Brouwer

namespace MS.Topology

/-- **Brouwer's fixed point theorem** for the closed unit ball of `EuclideanSpace ℝ (Fin n)`. -/

theorem no_smooth_retraction {U : Set E} (hU : IsOpen U) (hsub : closedBall (0 : E) 1 ⊆ U)
    {r : E → E} (hr : ContDiffOn ℝ 1 r U)
    (hnorm : ∀ x ∈ closedBall (0 : E) 1, ‖r x‖ = 1)
    (hfix : ∀ x ∈ sphere (0 : E) 1, r x = x) : False := by
  classical
  set μ : Measure E := Measure.addHaar with hμ
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ r x := fun x hx =>
    ((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)
  set V : E → (E →L[ℝ] E) := fun x => fderiv ℝ r x - ContinuousLinearMap.id ℝ E with hVdef
  have hVcont : ContinuousOn V U :=
    (hr.continuousOn_fderiv_of_isOpen hU le_rfl).sub continuousOn_const
  have hVcb : ContinuousOn V (closedBall (0 : E) 1) := hVcont.mono hsub
  have hvderiv : ∀ x ∈ U, HasFDerivAt (fun y => r y - y) (V x) x := fun x hx => by
    simpa [hVdef] using ((hdiff x hx).hasFDerivAt.sub (hasFDerivAt_id x))
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hVcb
  set L : ℝ := max L0 1 with hLdef
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hL : ∀ x ∈ closedBall (0 : E) 1, ‖V x‖ ≤ L := fun x hx => (hL0 x hx).trans (le_max_left _ _)
  set t₀ : ℝ := 1 / (2 * L) with ht₀def
  have ht₀pos : 0 < t₀ := by rw [ht₀def]; positivity
  have ht₀half : t₀ * L = 1 / 2 := by rw [ht₀def]; field_simp
  have ht₀le : t₀ ≤ 1 / 2 := by
    rw [ht₀def]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  -- The key computation: for small `t` the map `x ↦ x + t (r x - x)` preserves the ball.
  have key : ∀ t ∈ Icc (0 : ℝ) t₀,
      ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • V x).det ∂μ
        = (μ (ball (0 : E) 1)).toReal := by
    rintro t ⟨ht0, htt₀⟩
    have htle : t ≤ 1 / 2 := htt₀.trans ht₀le
    have htL' : t * L ≤ 1 / 2 := by
      calc t * L ≤ t₀ * L := by nlinarith
        _ = 1 / 2 := ht₀half
    have htL : ∀ x ∈ closedBall (0 : E) 1, t * ‖V x‖ ≤ 1 / 2 := by
      intro x hx
      have := hL x hx
      nlinarith [norm_nonneg (V x)]
    have hsmul : ∀ x ∈ closedBall (0 : E) 1, ‖t • V x‖ < 1 := by
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith [htL x hx]
    set f : E → E := fun x => x + t • (r x - x) with hfdef
    have hfd : ∀ x ∈ U, HasFDerivAt f (ContinuousLinearMap.id ℝ E + t • V x) x := fun x hx =>
      (hasFDerivAt_id x).add ((hvderiv x hx).const_smul t)
    have hfcont : ContinuousOn f (closedBall (0 : E) 1) := fun x hx =>
      ((hfd x (hsub hx)).continuousAt).continuousWithinAt
    have hfball : ∀ x ∈ ball (0 : E) 1, f x ∈ ball (0 : E) 1 := by
      intro x hx
      have hx1 : ‖x‖ < 1 := by simpa using hx
      have hrx : ‖r x‖ = 1 := hnorm x (ball_subset_closedBall hx)
      have hfx : f x = (1 - t) • x + t • r x := by rw [hfdef]; module
      rw [mem_ball_zero_iff, hfx]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * 1 := by
            rw [norm_smul, norm_smul, hrx, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
        _ < 1 := by nlinarith
    have hsph : ∀ x ∈ sphere (0 : E) 1, f x = x := by
      intro x hx; rw [hfdef]; simp [hfix x hx]
    -- injectivity
    have hlip : LipschitzOnWith (Real.toNNReal L) (fun y => r y - y) (closedBall (0 : E) 1) := by
      refine (convex_closedBall (0 : E) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun x hx => (hvderiv x (hsub hx)).hasFDerivWithinAt) ?_
      intro x hx
      have : (‖V x‖₊ : ℝ) ≤ ((Real.toNNReal L : ℝ≥0) : ℝ) := by
        rw [Real.coe_toNNReal _ hLpos.le]
        exact hL x hx
      exact_mod_cast this
    have hinj : InjOn f (closedBall (0 : E) 1) := by
      intro x hx y hy hxy
      have h1 : ‖(r x - x) - (r y - y)‖ ≤ L * ‖x - y‖ := by
        have h := hlip.dist_le_mul x hx y hy
        rw [dist_eq_norm, dist_eq_norm] at h
        simpa [Real.coe_toNNReal _ hLpos.le] using h
      have h2 : x - y = -(t • ((r x - x) - (r y - y))) := by
        have h3 : f x - f y = 0 := by rw [hxy]; simp
        rw [hfdef] at h3
        simp only at h3
        linear_combination (norm := module) h3
      have h4 : ‖x - y‖ ≤ t * (L * ‖x - y‖) :=
        calc ‖x - y‖ = t * ‖(r x - x) - (r y - y)‖ := by
              conv_lhs => rw [h2]
              rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
          _ ≤ t * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 ht0
      have h5 : ‖x - y‖ ≤ 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h5)
    -- `f` is an open map on the ball
    have hopenim : IsOpen (f '' (ball (0 : E) 1)) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hxU : x ∈ U := hsub (ball_subset_closedBall hx)
      obtain ⟨e, he⟩ := exists_equiv_id_add_smul (V x) (hsmul x (ball_subset_closedBall hx))
      have hcd : ContDiffAt ℝ 1 f x := by
        have hcr : ContDiffAt ℝ 1 r x := hr.contDiffAt (hU.mem_nhds hxU)
        exact contDiffAt_id.add (contDiffAt_const.smul (hcr.sub contDiffAt_id))
      have hstrict : HasStrictFDerivAt f (e : E →L[ℝ] E) x := by
        rw [he, ← (hfd x hxU).fderiv]
        exact hcd.hasStrictFDerivAt one_ne_zero
      rw [← hstrict.map_nhds_eq_of_equiv]
      exact Filter.image_mem_map (isOpen_ball.mem_nhds hx)
    have hclosedim : IsClosed (f '' (closedBall (0 : E) 1)) :=
      ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hfcont).isClosed
    -- points of the ball in the image of the closed ball come from the open ball
    have hfromball : ∀ z ∈ ball (0 : E) 1, z ∈ f '' (closedBall (0 : E) 1) →
        z ∈ f '' (ball (0 : E) 1) := by
      rintro z hz ⟨x, hx, rfl⟩
      rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with h | h
      · exact ⟨x, mem_ball_zero_iff.mpr h, rfl⟩
      · exfalso
        have hxs : x ∈ sphere (0 : E) 1 := by simp [h]
        rw [hsph x hxs, mem_ball_zero_iff, h] at hz
        exact lt_irrefl _ hz
    have himage : f '' (ball (0 : E) 1) = ball (0 : E) 1 := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩; exact hfball x hx
      · intro y hy
        by_contra hyn
        have hyC : y ∉ f '' (closedBall (0 : E) 1) := fun h => hyn (hfromball y hy h)
        have hpre : IsPreconnected (ball (0 : E) 1) := (convex_ball (0 : E) 1).isPreconnected
        have hcover : ball (0 : E) 1 ⊆
            f '' (ball (0 : E) 1) ∪ (f '' (closedBall (0 : E) 1))ᶜ := by
          intro z hz
          by_cases hzc : z ∈ f '' (closedBall (0 : E) 1)
          · exact Or.inl (hfromball z hz hzc)
          · exact Or.inr hzc
        obtain ⟨w, _, hw2, hw3⟩ := hpre _ _ hopenim hclosedim.isOpen_compl hcover
          ⟨f 0, hfball 0 (mem_ball_self one_pos), ⟨0, mem_ball_self one_pos, rfl⟩⟩ ⟨y, hy, hyC⟩
        obtain ⟨x, hx, hxw⟩ := hw2
        exact hw3 ⟨x, ball_subset_closedBall hx, hxw⟩
    -- change of variables
    have hdetpos : ∀ x ∈ ball (0 : E) 1,
        0 < (ContinuousLinearMap.id ℝ E + t • V x).det := fun x hx =>
      det_id_add_smul_pos (V x) ht0 (by linarith [htL x (ball_subset_closedBall hx)])
    have hcv : ∫⁻ x in ball (0 : E) 1,
        ENNReal.ofReal |(ContinuousLinearMap.id ℝ E + t • V x).det| ∂μ = μ (ball (0 : E) 1) := by
      conv_rhs => rw [← himage]
      exact lintegral_abs_det_fderiv_eq_addHaar_image μ measurableSet_ball
        (fun x hx => (hfd x (hsub (ball_subset_closedBall hx))).hasFDerivWithinAt)
        (hinj.mono ball_subset_closedBall)
    have hintg : IntegrableOn
        (fun x => (ContinuousLinearMap.id ℝ E + t • V x).det) (ball (0 : E) 1) μ :=
      (((continuousOn_det_id_add_smul hVcb t).integrableOn_compact
        (isCompact_closedBall _ _))).mono_set ball_subset_closedBall
    have hnonneg : 0 ≤ᵐ[μ.restrict (ball (0 : E) 1)]
        fun x => (ContinuousLinearMap.id ℝ E + t • V x).det := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using (hdetpos x hx).le
    rw [setLIntegral_congr_fun measurableSet_ball
      (fun x hx => by rw [abs_of_pos (hdetpos x hx)]),
      ← ofReal_integral_eq_lintegral_ofReal hintg hnonneg] at hcv
    rw [← hcv, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]
  -- the integral is a polynomial in `t`, constant on `[0, t₀]`, hence constant
  obtain ⟨q, hq⟩ := exists_polynomial_integral_det V hVcb
  set c : ℝ := (μ (ball (0 : E) 1)).toReal with hcdef
  have hsubroot : Icc (0 : ℝ) t₀ ⊆ {x | (q - Polynomial.C c).IsRoot x} := by
    intro t ht
    simp only [mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
      sub_eq_zero]
    rw [hq t]
    exact key t ht
  have hroots : q - Polynomial.C c = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono hsubroot (Set.Icc_infinite ht₀pos))
  have hq1 : q.eval 1 = c := by
    have h := congrArg (Polynomial.eval 1) hroots
    simpa [sub_eq_zero] using h
  have hzero : q.eval 1 = 0 := by
    rw [hq 1]
    have hz : ∀ x ∈ ball (0 : E) 1,
        (ContinuousLinearMap.id ℝ E + (1 : ℝ) • V x).det = 0 := by
      intro x hx
      have hEq : ContinuousLinearMap.id ℝ E + (1 : ℝ) • V x = fderiv ℝ r x := by
        simp [hVdef]
      rw [hEq]
      exact det_fderiv_eq_zero_of_norm_eq_one isOpen_ball hx
        (hdiff x (hsub (ball_subset_closedBall hx)))
        (fun y hy => hnorm y (ball_subset_closedBall hy))
    rw [setIntegral_congr_fun measurableSet_ball hz]
    simp
  have hcpos : 0 < c :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end NoRetraction

/-! ### Smooth approximation of continuous functions on a compact set -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Real valued Stone–Weierstrass: continuous functions on a compact subset of `E` are uniformly
approximated by restrictions of globally `C¹` functions. -/
