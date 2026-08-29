/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Real MeasureTheory
open scoped Topology BigOperators Classical

namespace Math2

/-! ## The Sato–Tate distribution -/

/-- The Sato–Tate density `(2/π) sin²θ` on `[0, π]`. -/
noncomputable def stDensity (x : ℝ) : ℝ := (2 / π) * Real.sin x ^ 2

/-- An explicit antiderivative of `stDensity`. -/
noncomputable def stCDF (t : ℝ) : ℝ := t / π - Real.sin (2 * t) / (2 * π)

lemma stDensity_nonneg (x : ℝ) : 0 ≤ stDensity x :=
  mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (sq_nonneg _)

lemma stDensity_le (x : ℝ) : stDensity x ≤ 2 / π := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have h : Real.sin x ^ 2 ≤ 1 := by
    have := Real.neg_one_le_sin x
    have := Real.sin_le_one x
    nlinarith
  have h2 : (0:ℝ) < 2 / π := by positivity
  calc stDensity x = (2/π) * Real.sin x ^ 2 := rfl
    _ ≤ (2/π) * 1 := by nlinarith
    _ = 2/π := by ring

lemma continuous_stDensity : Continuous stDensity := by
  unfold stDensity; fun_prop

lemma hasDerivAt_stCDF (t : ℝ) : HasDerivAt stCDF (stDensity t) t := by
  have hπ : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun t : ℝ => t / π) (1 / π) t := by
    simpa using (hasDerivAt_id t).div_const π
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * t) * 2) t := by
    have : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2:ℝ)
    simpa using (Real.hasDerivAt_sin (2 * t)).comp t this
  have h3 := h1.sub (h2.div_const (2 * π))
  convert h3 using 1
  have hcos : Real.cos (2 * t) = 1 - 2 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hcos]
  unfold stDensity
  field_simp
  ring

lemma integral_stDensity (u v : ℝ) :
    ∫ x in u..v, stDensity x = stCDF v - stCDF u := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_stCDF x)]
  exact (continuous_stDensity).intervalIntegrable u v

lemma stCDF_mono : Monotone stCDF := by
  intro u v huv
  have := integral_stDensity u v
  have hint : 0 ≤ ∫ x in u..v, stDensity x :=
    intervalIntegral.integral_nonneg huv (fun x _ => stDensity_nonneg x)
  linarith [this ▸ hint]

lemma stCDF_sub_le {u v : ℝ} (huv : u ≤ v) : stCDF v - stCDF u ≤ (2 / π) * (v - u) := by
  have h := integral_stDensity u v
  have hle : (∫ x in u..v, stDensity x) ≤ ∫ _ in u..v, (2 / π : ℝ) :=
    intervalIntegral.integral_mono_on huv
      (continuous_stDensity.intervalIntegrable u v)
      (intervalIntegrable_const) (fun x _ => stDensity_le x)
  rw [h, intervalIntegral.integral_const, smul_eq_mul] at hle
  nlinarith [hle]

/-! ## Trapezoidal test functions -/

/-- A continuous trapezoidal bump: it is `1` on `[c+δ, d-δ]`, `0` outside `(c,d)`,
and takes values in `[0,1]`. -/
noncomputable def trap (c d δ x : ℝ) : ℝ := max 0 (min 1 (min ((x - c) / δ) ((d - x) / δ)))

lemma continuous_trap (c d δ : ℝ) : Continuous (trap c d δ) := by
  unfold trap; fun_prop

lemma trap_nonneg (c d δ x : ℝ) : 0 ≤ trap c d δ x := le_max_left _ _

lemma trap_le_one (c d δ x : ℝ) : trap c d δ x ≤ 1 := by
  unfold trap
  exact max_le zero_le_one (min_le_left _ _)

lemma trap_eq_one {c d δ x : ℝ} (hδ : 0 < δ) (h1 : c + δ ≤ x) (h2 : x ≤ d - δ) :
    trap c d δ x = 1 := by
  have hx1 : 1 ≤ (x - c) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hx2 : 1 ≤ (d - x) / δ := by
    rw [le_div_iff₀ hδ]; linarith
  unfold trap
  rw [min_eq_left (le_min hx1 hx2)]
  simp

lemma trap_eq_zero_left {c d δ x : ℝ} (hδ : 0 < δ) (h : x ≤ c) : trap c d δ x = 0 := by
  have : (x - c) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  unfold trap
  have h2 : min ((x - c) / δ) ((d - x) / δ) ≤ 0 := le_trans (min_le_left _ _) this
  exact max_eq_left (le_trans (min_le_right _ _) h2)

lemma trap_eq_zero_right {c d δ x : ℝ} (hδ : 0 < δ) (h : d ≤ x) : trap c d δ x = 0 := by
  have : (d - x) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  unfold trap
  have h2 : min ((x - c) / δ) ((d - x) / δ) ≤ 0 := le_trans (min_le_right _ _) this
  exact max_eq_left (le_trans (min_le_right _ _) h2)

/-! ## Integral bounds for the trapezoids against the Sato–Tate density -/

lemma integral_trap_outer_le {a b δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    (∫ x in (0:ℝ)..π, trap (a - δ) (b + δ) δ x * stDensity x)
      ≤ (stCDF b - stCDF a) + (4 / π) * δ := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set f : ℝ → ℝ := fun x => trap (a - δ) (b + δ) δ x * stDensity x with hf
  have hcont : Continuous f := (continuous_trap _ _ _).mul continuous_stDensity
  set c : ℝ := max 0 (a - δ) with hc
  set d : ℝ := min π (b + δ) with hd
  have hc0 : 0 ≤ c := le_max_left _ _
  have hdpi : d ≤ π := min_le_left _ _
  have hcd : c ≤ d := by
    refine max_le (le_min hpi.le (by linarith)) (le_min (by linarith) (by linarith))
  have hsplit : (∫ x in (0:ℝ)..c, f x) + (∫ x in c..d, f x) + (∫ x in d..π, f x)
      = ∫ x in (0:ℝ)..π, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hzero1 : (∫ x in (0:ℝ)..c, f x) = 0 := by
    rcases le_or_gt (a - δ) 0 with h | h
    · rw [show c = 0 from max_eq_left h, intervalIntegral.integral_same]
    · have hce : c = a - δ := max_eq_right h.le
      rw [hce]
      have heq : (∫ x in (0:ℝ)..(a - δ), f x) = ∫ _ in (0:ℝ)..(a - δ), (0:ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [Set.uIcc_of_le h.le] at hx
        simp only [hf]
        rw [trap_eq_zero_left hδ hx.2, zero_mul]
      simp [heq]
  have hzero2 : (∫ x in d..π, f x) = 0 := by
    rcases le_or_gt π (b + δ) with h | h
    · rw [show d = π from min_eq_left h, intervalIntegral.integral_same]
    · have hde : d = b + δ := min_eq_right h.le
      rw [hde]
      have heq : (∫ x in (b + δ)..π, f x) = ∫ _ in (b + δ)..π, (0:ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [Set.uIcc_of_le h.le] at hx
        simp only [hf]
        rw [trap_eq_zero_right hδ hx.1, zero_mul]
      simp [heq]
  have hmid : (∫ x in c..d, f x) ≤ stCDF d - stCDF c := by
    rw [← integral_stDensity]
    refine intervalIntegral.integral_mono_on hcd (hcont.intervalIntegrable _ _)
      (continuous_stDensity.intervalIntegrable _ _) ?_
    intro x _
    exact mul_le_of_le_one_left (stDensity_nonneg x) (trap_le_one _ _ _ _)
  have hmono1 : stCDF d ≤ stCDF (b + δ) := stCDF_mono (min_le_right _ _)
  have hmono2 : stCDF (a - δ) ≤ stCDF c := stCDF_mono (le_max_right _ _)
  have e1 : stCDF (b + δ) - stCDF b ≤ (2 / π) * δ := by
    have := stCDF_sub_le (show b ≤ b + δ by linarith)
    have hbd : b + δ - b = δ := by ring
    rw [hbd] at this
    exact this
  have e2 : stCDF a - stCDF (a - δ) ≤ (2 / π) * δ := by
    have := stCDF_sub_le (show a - δ ≤ a by linarith)
    have had : a - (a - δ) = δ := by ring
    rw [had] at this
    exact this
  have esum : (2 / π) * δ + (2 / π) * δ = (4 / π) * δ := by ring
  linarith [hsplit, hzero1, hzero2, hmid, hmono1, hmono2, e1, e2]

lemma integral_trap_inner_ge {a b δ : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    (stCDF b - stCDF a) - (4 / π) * δ
      ≤ ∫ x in (0:ℝ)..π, trap a b δ x * stDensity x := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  set f : ℝ → ℝ := fun x => trap a b δ x * stDensity x with hf
  have hcont : Continuous f := (continuous_trap _ _ _).mul continuous_stDensity
  have hfnonneg : ∀ x, 0 ≤ f x := fun x =>
    mul_nonneg (trap_nonneg _ _ _ _) (stDensity_nonneg x)
  rcases lt_or_ge (b - δ) (a + δ) with hcase | hcase
  · have h0 : 0 ≤ ∫ x in (0:ℝ)..π, f x :=
      intervalIntegral.integral_nonneg hpi.le (fun x _ => hfnonneg x)
    have hsub := stCDF_sub_le hab
    have hle : (2 / π) * (b - a) ≤ (2 / π) * (2 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have heq : (2 / π) * (2 * δ) = (4 / π) * δ := by ring
    linarith
  · have hac : 0 ≤ a + δ := by linarith
    have hdpi : b - δ ≤ π := by linarith
    have hsplit : (∫ x in (0:ℝ)..(a + δ), f x) + (∫ x in (a + δ)..(b - δ), f x)
        + (∫ x in (b - δ)..π, f x) = ∫ x in (0:ℝ)..π, f x := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have h1 : 0 ≤ ∫ x in (0:ℝ)..(a + δ), f x :=
      intervalIntegral.integral_nonneg hac (fun x _ => hfnonneg x)
    have h3 : 0 ≤ ∫ x in (b - δ)..π, f x :=
      intervalIntegral.integral_nonneg hdpi (fun x _ => hfnonneg x)
    have h2 : (∫ x in (a + δ)..(b - δ), f x) = stCDF (b - δ) - stCDF (a + δ) := by
      rw [← integral_stDensity]
      refine intervalIntegral.integral_congr ?_
      intro x hx
      rw [Set.uIcc_of_le hcase] at hx
      simp only [hf]
      rw [trap_eq_one hδ hx.1 hx.2, one_mul]
    have e1 : stCDF b - stCDF (b - δ) ≤ (2 / π) * δ := by
      have := stCDF_sub_le (show b - δ ≤ b by linarith)
      have hbd : b - (b - δ) = δ := by ring
      rw [hbd] at this
      exact this
    have e2 : stCDF (a + δ) - stCDF a ≤ (2 / π) * δ := by
      have := stCDF_sub_le (show a ≤ a + δ by linarith)
      have had : a + δ - a = δ := by ring
      rw [had] at this
      exact this
    have esum : (2 / π) * δ + (2 / π) * δ = (4 / π) * δ := by ring
    linarith

/-! ## From convergence against continuous test functions to counting in intervals -/

lemma equidistribution_of_testFunctions {θ : ℕ → ℝ} {N : ℕ → ℝ}
    (hN : ∀ X, 0 ≤ N X)
    (hST : ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun X => (∑ p ∈ Nat.primesBelow X, f (θ p)) / N X) atTop
        (𝓝 (∫ x in (0:ℝ)..π, f x * stDensity x)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    Tendsto
      (fun X => (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X)
      atTop (𝓝 (stCDF b - stCDF a)) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := min 1 (π * ε / 16) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδε : (4 / π) * δ ≤ ε / 4 := by
    have h1 : δ ≤ π * ε / 16 := min_le_right _ _
    have h2 : (4 / π) * δ ≤ (4 / π) * (π * ε / 16) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (4 / π) * (π * ε / 16) = ε / 4 := by field_simp; ring
    linarith
  obtain ⟨X1, hX1⟩ := Metric.tendsto_atTop.1
    (hST (trap (a - δ) (b + δ) δ) (continuous_trap _ _ _)) (ε / 4) (by linarith)
  obtain ⟨X2, hX2⟩ := Metric.tendsto_atTop.1
    (hST (trap a b δ) (continuous_trap _ _ _)) (ε / 4) (by linarith)
  refine ⟨max X1 X2, fun X hX => ?_⟩
  have h1 := hX1 X (le_of_max_le_left hX)
  have h2 := hX2 X (le_of_max_le_right hX)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hdiv : ∀ x y : ℝ, x ≤ y → x / N X ≤ y / N X := by
    intro x y h
    rcases (hN X).lt_or_eq with h0 | h0
    · gcongr
    · simp [← h0]
  have hcard : (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ)
      = ∑ p ∈ Nat.primesBelow X, if θ p ∈ Set.Icc a b then (1:ℝ) else 0 := by
    rw [Finset.card_filter]
    push_cast
    rfl
  have hup : (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X
      ≤ (∑ p ∈ Nat.primesBelow X, trap (a - δ) (b + δ) δ (θ p)) / N X := by
    rw [hcard]
    refine hdiv _ _ (Finset.sum_le_sum ?_)
    intro p _
    by_cases hp : θ p ∈ Set.Icc a b
    · rw [if_pos hp, trap_eq_one hδ (by have := hp.1; linarith) (by have := hp.2; linarith)]
    · rw [if_neg hp]
      exact trap_nonneg _ _ _ _
  have hlow : (∑ p ∈ Nat.primesBelow X, trap a b δ (θ p)) / N X
      ≤ (((Nat.primesBelow X).filter (fun p => θ p ∈ Set.Icc a b)).card : ℝ) / N X := by
    rw [hcard]
    refine hdiv _ _ (Finset.sum_le_sum ?_)
    intro p _
    by_cases hp : θ p ∈ Set.Icc a b
    · rw [if_pos hp]
      exact trap_le_one _ _ _ _
    · rw [if_neg hp]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp
      rcases hp with hp | hp
      · exact le_of_eq (trap_eq_zero_left hδ hp.le)
      · exact le_of_eq (trap_eq_zero_right hδ hp.le)
  have hI1 := integral_trap_outer_le hδ ha hab hb
  have hI2 := integral_trap_inner_ge hδ ha hab hb
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ## Chebyshev polynomials and the Sato–Tate measure -/

/-- `UBasis k x = U_k(cos x)`, where `U_k` is the `k`-th Chebyshev polynomial of the second
kind.  Equivalently `UBasis k x = sin ((k+1) x) / sin x`; these are the traces of the
symmetric powers of a `SU(2)`-conjugacy class with angle `x`. -/
noncomputable def UBasis (k : ℕ) : ℝ → ℝ :=
  fun x => (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.cos x)

lemma continuous_UBasis (k : ℕ) : Continuous (UBasis k) := by
  unfold UBasis
  exact (Polynomial.Chebyshev.U ℝ (k : ℤ)).continuous_aeval.comp Real.continuous_cos

lemma UBasis_zero : UBasis 0 = fun _ => (1:ℝ) := by
  funext x
  simp [UBasis, Polynomial.Chebyshev.U_zero]

lemma UBasis_mul_sin (k : ℕ) (x : ℝ) :
    UBasis k x * Real.sin x = Real.sin ((k + 1) * x) := by
  simp [UBasis, Polynomial.Chebyshev.U_real_cos]

lemma integral_sin_mul_sin {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0:ℝ)..π, Real.sin (((n : ℝ) + 1) * x) * Real.sin x) = 0 := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set G : ℝ → ℝ := fun x =>
    Real.sin ((n : ℝ) * x) / (2 * n) - Real.sin (((n : ℝ) + 2) * x) / (2 * ((n : ℝ) + 2)) with hG
  have hderiv : ∀ x : ℝ, HasDerivAt G (Real.sin (((n : ℝ) + 1) * x) * Real.sin x) x := by
    intro x
    have hl1 : HasDerivAt (fun x : ℝ => (n : ℝ) * x) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ))
    have hl2 : HasDerivAt (fun x : ℝ => ((n : ℝ) + 2) * x) ((n : ℝ) + 2) x := by
      simpa using (hasDerivAt_id x).const_mul ((n : ℝ) + 2)
    have h1 : HasDerivAt (fun x : ℝ => Real.sin ((n : ℝ) * x))
        (Real.cos ((n : ℝ) * x) * (n : ℝ)) x := by
      simpa using (Real.hasDerivAt_sin ((n : ℝ) * x)).comp x hl1
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (((n : ℝ) + 2) * x))
        (Real.cos (((n : ℝ) + 2) * x) * ((n : ℝ) + 2)) x := by
      simpa using (Real.hasDerivAt_sin (((n : ℝ) + 2) * x)).comp x hl2
    have h3 := (h1.div_const (2 * (n:ℝ))).sub (h2.div_const (2 * ((n : ℝ) + 2)))
    convert h3 using 1
    have key : Real.cos ((n:ℝ) * x) - Real.cos (((n:ℝ) + 2) * x)
        = 2 * Real.sin (((n:ℝ) + 1) * x) * Real.sin x := by
      have h := Real.cos_sub_cos ((n:ℝ) * x) (((n:ℝ) + 2) * x)
      have e1 : ((n:ℝ) * x + ((n:ℝ) + 2) * x) / 2 = ((n:ℝ) + 1) * x := by ring
      have e2 : ((n:ℝ) * x - ((n:ℝ) + 2) * x) / 2 = -x := by ring
      rw [h, e1, e2, Real.sin_neg]
      ring
    have hne1 : (n:ℝ) ≠ 0 := ne_of_gt hn0
    have r1 : Real.cos ((n:ℝ) * x) * (n:ℝ) / (2 * (n:ℝ)) = Real.cos ((n:ℝ) * x) / 2 := by
      field_simp
    have r2 : Real.cos (((n:ℝ) + 2) * x) * ((n:ℝ) + 2) / (2 * ((n:ℝ) + 2))
        = Real.cos (((n:ℝ) + 2) * x) / 2 := by
      have : ((n:ℝ) + 2) ≠ 0 := by positivity
      field_simp
    rw [r1, r2]
    linarith [key]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) 0 π)]
  have hs1 : Real.sin ((n : ℝ) * π) = 0 := Real.sin_nat_mul_pi n
  have hs2 : Real.sin (((n : ℝ) + 2) * π) = 0 := by
    have : ((n : ℝ) + 2) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact Real.sin_nat_mul_pi (n + 2)
  simp [hG, hs1, hs2]

lemma integral_UBasis_mul_stDensity {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (0:ℝ)..π, UBasis n x * stDensity x) = 0 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hcongr : (∫ x in (0:ℝ)..π, UBasis n x * stDensity x)
      = ∫ x in (0:ℝ)..π, (2 / π) * (Real.sin (((n : ℝ) + 1) * x) * Real.sin x) := by
    refine intervalIntegral.integral_congr ?_
    intro x _
    have h := UBasis_mul_sin n x
    simp only [stDensity]
    rw [← h]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_sin_mul_sin hn, mul_zero]

lemma integral_UBasis_zero_mul_stDensity :
    (∫ x in (0:ℝ)..π, UBasis 0 x * stDensity x) = 1 := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have : (∫ x in (0:ℝ)..π, UBasis 0 x * stDensity x) = ∫ x in (0:ℝ)..π, stDensity x := by
    simp [UBasis_zero]
  rw [this, integral_stDensity]
  simp [stCDF, Real.sin_two_pi, Real.pi_ne_zero]

/-! ## The span of the Chebyshev functions -/

/-- The `ℝ`-linear span of the functions `x ↦ U_k (cos x)` inside `ℝ → ℝ`. -/
noncomputable def USpan : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Set.range UBasis)

lemma UBasis_mem_USpan (k : ℕ) : UBasis k ∈ USpan := Submodule.subset_span ⟨k, rfl⟩

lemma cos_mul_UBasis_zero (x : ℝ) : Real.cos x * UBasis 0 x = UBasis 1 x / 2 := by
  simp [UBasis, Polynomial.Chebyshev.U_zero, Polynomial.Chebyshev.U_one]

lemma cos_mul_UBasis_succ (j : ℕ) (x : ℝ) :
    Real.cos x * UBasis (j + 1) x = (UBasis (j + 2) x + UBasis j x) / 2 := by
  have h := Polynomial.Chebyshev.U_add_two (R := ℝ) (n := (j : ℤ))
  have h' : (Polynomial.Chebyshev.U ℝ ((j : ℤ) + 2)).eval (Real.cos x)
      = 2 * Real.cos x * (Polynomial.Chebyshev.U ℝ ((j : ℤ) + 1)).eval (Real.cos x)
        - (Polynomial.Chebyshev.U ℝ (j : ℤ)).eval (Real.cos x) := by
    rw [h]
    simp
  have e1 : (((j + 2 : ℕ)) : ℤ) = (j : ℤ) + 2 := by push_cast; ring
  have e2 : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  simp only [UBasis, e1, e2]
  rw [h']
  ring

lemma cos_mul_mem_USpan {g : ℝ → ℝ} (hg : g ∈ USpan) :
    (fun x => Real.cos x * g x) ∈ USpan := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      match k with
      | 0 =>
          have : (fun x => Real.cos x * UBasis 0 x) = (1/2 : ℝ) • UBasis 1 := by
            funext x
            simp [cos_mul_UBasis_zero x]
            ring
          rw [this]
          exact Submodule.smul_mem _ _ (UBasis_mem_USpan 1)
      | (j+1) =>
          have : (fun x => Real.cos x * UBasis (j + 1) x)
              = (1/2 : ℝ) • UBasis (j + 2) + (1/2 : ℝ) • UBasis j := by
            funext x
            simp [cos_mul_UBasis_succ j x]
            ring
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (UBasis_mem_USpan (j + 2)))
            (Submodule.smul_mem _ _ (UBasis_mem_USpan j))
  | zero =>
      have : (fun x => Real.cos x * (0 : ℝ → ℝ) x) = 0 := by funext x; simp
      rw [this]
      exact Submodule.zero_mem _
  | add g h _ _ ih1 ih2 =>
      have : (fun x => Real.cos x * (g + h) x)
          = (fun x => Real.cos x * g x) + (fun x => Real.cos x * h x) := by
        funext x; simp [mul_add]
      rw [this]
      exact Submodule.add_mem _ ih1 ih2
  | smul c g _ ih =>
      have : (fun x => Real.cos x * (c • g) x) = c • (fun x => Real.cos x * g x) := by
        funext x; simp [mul_comm, mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ _ ih

lemma cos_pow_mem_USpan (m : ℕ) : (fun x : ℝ => Real.cos x ^ m) ∈ USpan := by
  induction m with
  | zero =>
      have : (fun x : ℝ => Real.cos x ^ 0) = UBasis 0 := by
        funext x; simp [UBasis_zero]
      rw [this]
      exact UBasis_mem_USpan 0
  | succ m ih =>
      have : (fun x : ℝ => Real.cos x ^ (m + 1)) = fun x => Real.cos x * Real.cos x ^ m := by
        funext x; ring
      rw [this]
      exact cos_mul_mem_USpan ih

lemma polyCos_mem_USpan (P : Polynomial ℝ) :
    (fun x : ℝ => P.eval (Real.cos x)) ∈ USpan := by
  have hrw : (fun x : ℝ => P.eval (Real.cos x))
      = ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i) • (fun x : ℝ => Real.cos x ^ i) := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
    simp [Finset.sum_apply]
  rw [hrw]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (cos_pow_mem_USpan i))

lemma continuous_of_mem_USpan {g : ℝ → ℝ} (hg : g ∈ USpan) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem g hg => obtain ⟨k, rfl⟩ := hg; exact continuous_UBasis k
  | zero => exact continuous_const
  | add g h _ _ ih1 ih2 => exact ih1.add ih2
  | smul c g _ ih => exact ih.const_smul c

/-! ## The averaging law -/

/-- The empirical average of `f` over the angles attached to the primes below `X`. -/
noncomputable def primeAvg (θ : ℕ → ℝ) (f : ℝ → ℝ) (X : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesBelow X, f (θ p)) / ((Nat.primesBelow X).card : ℝ)

/-- `f` obeys the Sato–Tate averaging law along the angles `θ`. -/
def STAverage (θ : ℕ → ℝ) (f : ℝ → ℝ) : Prop :=
  Tendsto (primeAvg θ f) atTop (𝓝 (∫ x in (0:ℝ)..π, f x * stDensity x))

lemma primeAvg_add (θ : ℕ → ℝ) (f g : ℝ → ℝ) :
    primeAvg θ (f + g) = fun X => primeAvg θ f X + primeAvg θ g X := by
  funext X
  simp only [primeAvg, Pi.add_apply]
  rw [Finset.sum_add_distrib, add_div]

lemma primeAvg_sub (θ : ℕ → ℝ) (f g : ℝ → ℝ) (X : ℕ) :
    primeAvg θ (fun x => f x - g x) X = primeAvg θ f X - primeAvg θ g X := by
  simp only [primeAvg]
  rw [Finset.sum_sub_distrib, sub_div]

lemma primeAvg_smul (θ : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    primeAvg θ (c • f) = fun X => c * primeAvg θ f X := by
  funext X
  simp only [primeAvg, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_div_assoc]

lemma primesBelow_card_pos {X : ℕ} (hX : 3 ≤ X) : 0 < (Nat.primesBelow X).card :=
  Finset.card_pos.2 ⟨2, Nat.mem_primesBelow.2 ⟨by omega, Nat.prime_two⟩⟩

lemma STAverage_add {θ : ℕ → ℝ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfa : STAverage θ f) (hga : STAverage θ g) : STAverage θ (f + g) := by
  have hint : (∫ x in (0:ℝ)..π, (f + g) x * stDensity x)
      = (∫ x in (0:ℝ)..π, f x * stDensity x) + ∫ x in (0:ℝ)..π, g x * stDensity x := by
    have hc : (∫ x in (0:ℝ)..π, (f + g) x * stDensity x)
        = ∫ x in (0:ℝ)..π, (f x * stDensity x + g x * stDensity x) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      simp [add_mul]
    rw [hc]
    exact intervalIntegral.integral_add ((hf.mul continuous_stDensity).intervalIntegrable _ _)
      ((hg.mul continuous_stDensity).intervalIntegrable _ _)
  rw [STAverage, hint, primeAvg_add]
  exact hfa.add hga

lemma STAverage_smul {θ : ℕ → ℝ} {f : ℝ → ℝ} (c : ℝ)
    (hfa : STAverage θ f) : STAverage θ (c • f) := by
  have hint : (∫ x in (0:ℝ)..π, (c • f) x * stDensity x)
      = c * ∫ x in (0:ℝ)..π, f x * stDensity x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    simp [mul_assoc]
  rw [STAverage, hint, primeAvg_smul]
  exact hfa.const_mul c

lemma STAverage_zero {θ : ℕ → ℝ} : STAverage θ 0 := by
  have hint : (∫ x in (0:ℝ)..π, (0 : ℝ → ℝ) x * stDensity x) = 0 := by simp
  have havg : primeAvg θ 0 = fun _ => (0:ℝ) := by
    funext X; simp [primeAvg]
  rw [STAverage, hint, havg]
  exact tendsto_const_nhds

lemma STAverage_UBasis_zero {θ : ℕ → ℝ} : STAverage θ (UBasis 0) := by
  rw [STAverage, integral_UBasis_zero_mul_stDensity]
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1:ℝ)))
  filter_upwards [Filter.eventually_ge_atTop 3] with X hX
  have hpos : 0 < (Nat.primesBelow X).card := primesBelow_card_pos hX
  have hne : ((Nat.primesBelow X).card : ℝ) ≠ 0 := by positivity
  simp only [primeAvg, UBasis_zero]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, div_self hne]

lemma STAverage_UBasis {θ : ℕ → ℝ}
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0)) (k : ℕ) :
    STAverage θ (UBasis k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact STAverage_UBasis_zero
  · rw [STAverage, integral_UBasis_mul_stDensity hk]
    exact hmom k hk

lemma STAverage_of_mem_USpan {θ : ℕ → ℝ}
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0))
    {g : ℝ → ℝ} (hg : g ∈ USpan) : STAverage θ g := by
  have key : ∀ h ∈ USpan, Continuous h ∧ STAverage θ h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
        obtain ⟨k, rfl⟩ := hh
        exact ⟨continuous_UBasis k, STAverage_UBasis hmom k⟩
    | zero => exact ⟨continuous_const, STAverage_zero⟩
    | add h1 h2 _ _ ih1 ih2 =>
        exact ⟨ih1.1.add ih2.1, STAverage_add ih1.1 ih2.1 ih1.2 ih2.2⟩
    | smul c h _ ih => exact ⟨ih.1.const_smul c, STAverage_smul c ih.2⟩
  exact (key g hg).2

lemma abs_primeAvg_le {θ : ℕ → ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hθ : ∀ p, θ p ∈ Set.Icc (0:ℝ) π) (hM : 0 ≤ M)
    (hu : ∀ x ∈ Set.Icc (0:ℝ) π, |u x| ≤ M) (X : ℕ) : |primeAvg θ u X| ≤ M := by
  rcases Nat.eq_zero_or_pos (Nat.primesBelow X).card with h | h
  · rw [Finset.card_eq_zero] at h
    simp [primeAvg, h, hM]
  · have hcpos : (0:ℝ) < ((Nat.primesBelow X).card : ℝ) := by exact_mod_cast h
    rw [primeAvg, abs_div, abs_of_nonneg hcpos.le, div_le_iff₀ hcpos]
    calc |∑ p ∈ Nat.primesBelow X, u (θ p)|
        ≤ ∑ p ∈ Nat.primesBelow X, |u (θ p)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ Nat.primesBelow X, M := Finset.sum_le_sum (fun p _ => hu _ (hθ p))
      _ = M * ((Nat.primesBelow X).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma abs_integral_le_of_bound {u : ℝ → ℝ} {M : ℝ} (hu' : Continuous u)
    (hu : ∀ x ∈ Set.Icc (0:ℝ) π, |u x| ≤ M) :
    |∫ x in (0:ℝ)..π, u x * stDensity x| ≤ M := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have h1 : |∫ x in (0:ℝ)..π, u x * stDensity x| ≤ ∫ x in (0:ℝ)..π, |u x * stDensity x| :=
    intervalIntegral.abs_integral_le_integral_abs hpi.le
  have h2 : (∫ x in (0:ℝ)..π, |u x * stDensity x|) ≤ ∫ x in (0:ℝ)..π, M * stDensity x := by
    refine intervalIntegral.integral_mono_on hpi.le
      (((hu'.mul continuous_stDensity).abs).intervalIntegrable _ _)
      ((continuous_const.mul continuous_stDensity).intervalIntegrable _ _) ?_
    intro x hx
    rw [abs_mul, abs_of_nonneg (stDensity_nonneg x)]
    exact mul_le_mul_of_nonneg_right (hu x hx) (stDensity_nonneg x)
  have h3 : (∫ x in (0:ℝ)..π, M * stDensity x) = M := by
    rw [intervalIntegral.integral_const_mul, integral_stDensity]
    simp [stCDF, Real.sin_two_pi, Real.pi_ne_zero]
  linarith

/-- The Weyl criterion: if all the Chebyshev (symmetric power) moments tend to zero, then the
angles are equidistributed with respect to the Sato–Tate measure, tested against arbitrary
continuous functions. -/
lemma STAverage_of_continuous {θ : ℕ → ℝ} (hθ : ∀ p, θ p ∈ Set.Icc (0:ℝ) π)
    (hmom : ∀ n : ℕ, 1 ≤ n → Tendsto (primeAvg θ (UBasis n)) atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Continuous f) : STAverage θ f := by
  rw [STAverage, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun y => f (Real.arccos y)) (by fun_prop) (ε / 3) (by linarith)
  set g : ℝ → ℝ := fun x => P.eval (Real.cos x) with hgdef
  have hgcont : Continuous g := by
    exact (P.continuous_aeval).comp Real.continuous_cos
  have hgood : STAverage θ g := STAverage_of_mem_USpan hmom (polyCos_mem_USpan P)
  have hclose : ∀ x ∈ Set.Icc (0:ℝ) π, |f x - g x| ≤ ε / 3 := by
    intro x hx
    have h1 : Real.cos x ∈ Set.Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
    have h2 := hP (Real.cos x) h1
    rw [Real.arccos_cos hx.1 hx.2] at h2
    rw [abs_sub_comm]
    exact h2.le
  have hb1 : ∀ X, |primeAvg θ f X - primeAvg θ g X| ≤ ε / 3 := by
    intro X
    rw [← primeAvg_sub]
    exact abs_primeAvg_le hθ (by linarith) (fun x hx => hclose x hx) X
  have hb2 : |(∫ x in (0:ℝ)..π, f x * stDensity x) - ∫ x in (0:ℝ)..π, g x * stDensity x|
      ≤ ε / 3 := by
    have hsub : (∫ x in (0:ℝ)..π, (f x - g x) * stDensity x)
        = (∫ x in (0:ℝ)..π, f x * stDensity x) - ∫ x in (0:ℝ)..π, g x * stDensity x := by
      have hc : (∫ x in (0:ℝ)..π, (f x - g x) * stDensity x)
          = ∫ x in (0:ℝ)..π, (f x * stDensity x - g x * stDensity x) := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        simp [sub_mul]
      rw [hc]
      exact intervalIntegral.integral_sub
        ((hf.mul continuous_stDensity).intervalIntegrable _ _)
        ((hgcont.mul continuous_stDensity).intervalIntegrable _ _)
    rw [← hsub]
    exact abs_integral_le_of_bound (hf.sub hgcont) hclose
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.1 hgood (ε / 3) (by linarith)
  refine ⟨X0, fun X hX => ?_⟩
  have h3 := hX0 X hX
  rw [Real.dist_eq] at h3 ⊢
  have h1 := abs_le.1 (hb1 X)
  have h2 := abs_le.1 hb2
  have h4 := abs_lt.1 h3
  rw [abs_lt]
  constructor <;> linarith

/-! ## Frobenius angles of an elliptic curve -/

/-- The number of affine points of the Weierstrass curve `y² = x³ + A x + B` over `ZMod p`. -/
noncomputable def affinePointCount (A B : ℤ) (p : ℕ) : ℕ :=
  Nat.card {P : ZMod p × ZMod p // P.2 ^ 2 = P.1 ^ 3 + (A : ZMod p) * P.1 + (B : ZMod p)}

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)`, computed from the affine point count
(the projective point count is the affine one plus the point at infinity). -/
noncomputable def frobTrace (A B : ℤ) (p : ℕ) : ℤ := (p : ℤ) - (affinePointCount A B p : ℤ)

/-- The Frobenius angle `θ_p ∈ [0, π]`, defined by `a_p = 2 √p cos θ_p`. -/
noncomputable def frobAngle (A B : ℤ) (p : ℕ) : ℝ :=
  Real.arccos ((frobTrace A B p : ℝ) / (2 * Real.sqrt p))

/-- **Sato–Tate distribution of Frobenius angles.**

Let `E : y² = x³ + A x + B` be an elliptic curve over `ℚ`, and let `θ_p ∈ [0, π]` be its
Frobenius angles, defined by `a_p = 2 √p cos θ_p`, where `a_p = p + 1 - #E(𝔽_p)`
(computed here from the affine point count of the reduction of the given Weierstrass model).

The hypothesis `hmom` is the analytic input of the Sato–Tate theorem, the vanishing of all the
symmetric power moments: for every `n ≥ 1` the averages over the primes `p < X` of
`U_n(cos θ_p) = sin((n+1)θ_p) / sin θ_p` — the trace of Frobenius on the `n`-th symmetric power
— tend to `0`.  This is exactly what the potential automorphy of all symmetric powers gives for
an elliptic curve without complex multiplication; for a CM curve it fails already for `n = 2`.

The conclusion is the Sato–Tate distribution law: for every subinterval `[a,b] ⊆ [0,π]`, the
proportion of primes `p < X` whose Frobenius angle lies in `[a,b]` converges to
`∫_a^b (2/π) sin²θ dθ`, the measure of `[a,b]` for the Sato–Tate measure. -/
theorem sato_tate (A B : ℤ)
    (hmom : ∀ n : ℕ, 1 ≤ n →
      Tendsto (fun X => (∑ p ∈ Nat.primesBelow X,
          (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos (frobAngle A B p)))
            / ((Nat.primesBelow X).card : ℝ)) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    Tendsto
      (fun X => (((Nat.primesBelow X).filter
          (fun p => frobAngle A B p ∈ Set.Icc a b)).card : ℝ) / ((Nat.primesBelow X).card : ℝ))
      atTop (𝓝 (∫ x in a..b, (2 / π) * Real.sin x ^ 2)) := by
  have hθ : ∀ p, frobAngle A B p ∈ Set.Icc (0:ℝ) π := fun p =>
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hmom' : ∀ n : ℕ, 1 ≤ n →
      Tendsto (primeAvg (frobAngle A B) (UBasis n)) atTop (𝓝 0) := hmom
  have hST : ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun X => (∑ p ∈ Nat.primesBelow X, f (frobAngle A B p)) /
          ((Nat.primesBelow X).card : ℝ)) atTop
        (𝓝 (∫ x in (0:ℝ)..π, f x * stDensity x)) :=
    fun f hf => STAverage_of_continuous hθ hmom' hf
  have h := equidistribution_of_testFunctions (θ := frobAngle A B)
    (N := fun X => ((Nat.primesBelow X).card : ℝ)) (fun X => Nat.cast_nonneg _) hST ha hab hb
  rw [show (∫ x in a..b, (2 / π) * Real.sin x ^ 2) = stCDF b - stCDF a from
    integral_stDensity a b]
  exact h

end Math2

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

