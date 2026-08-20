import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

theorem logRepr {l : ℝ} (hl : 0 < l) :
    (IntegrableOn (fun t : ℝ => 1/(1+t) - 1/(l+t)) (Set.Ioi 0)) ∧
      ∫ t in Set.Ioi (0:ℝ), (1/(1+t) - 1/(l+t)) = Real.log l := by
  set g : ℝ → ℝ := fun t => Real.log (1+t) - Real.log (l+t) with hg
  have hderiv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt g (1/(1+t) - 1/(l+t)) t := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    have h1 : HasDerivAt (fun t : ℝ => Real.log (1+t)) (1/(1+t)) t := by
      have := (Real.hasDerivAt_log (x := 1+t) (by positivity)).comp t
        ((hasDerivAt_id t).const_add 1)
      simpa [one_div] using this
    have h2 : HasDerivAt (fun t : ℝ => Real.log (l+t)) (1/(l+t)) t := by
      have := (Real.hasDerivAt_log (x := l+t) (by positivity)).comp t
        ((hasDerivAt_id t).const_add l)
      simpa [one_div] using this
    exact h1.sub h2
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.sub
    · exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
    · exact (Real.continuousAt_log (by simpa using hl.ne')).comp (by fun_prop)
  have htend : Tendsto g atTop (𝓝 0) := by
    have hdiv : Tendsto (fun t : ℝ => (1 - l)/(l+t)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_left _ l tendsto_id
    have h1 : Tendsto (fun t : ℝ => (1+t)/(l+t)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => 1 + (1 - l)/(l+t)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hdiv
      rw [add_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      field_simp
      ring
    have h2 : Tendsto (fun t : ℝ => Real.log ((1+t)/(l+t))) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto.comp h1
    rw [Real.log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.log_div (by positivity) (by positivity)]
  have hg0 : g 0 = - Real.log l := by simp [hg]
  have hint : IntegrableOn (fun t : ℝ => 1/(1+t) - 1/(l+t)) (Set.Ioi 0) := by
    rcases le_total 1 l with h | h
    · refine integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun t ht => ?_) htend
      simp only [Set.mem_Ioi] at ht
      rw [sub_nonneg, one_div, one_div]
      exact inv_anti₀ (by positivity) (by linarith)
    · have hneg : IntegrableOn (fun t : ℝ => -(1/(1+t) - 1/(l+t))) (Set.Ioi 0) := by
        refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -g t) (hcont.neg)
          (fun t ht => (hderiv t ht).neg) (fun t ht => ?_) (by simpa using htend.neg)
        simp only [Set.mem_Ioi] at ht
        rw [neg_nonneg, sub_nonpos, one_div, one_div]
        exact inv_anti₀ (by positivity) (by linarith)
      have h3 := hneg.neg
      simp only [Pi.neg_def, neg_neg] at h3
      exact h3
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend, hg0]
  ring

/-- The integrand of the integral representation of the logarithm's quadratic form. -/
