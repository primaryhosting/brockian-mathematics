import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Contents

`Math2.carleson` : the Fourier series of a square-integrable function on the circle
`AddCircle 1` converges to it almost everywhere.  The statement takes as an explicit hypothesis
the key intermediate result `Math2.CarlesonWeakL2 C`, the Carleson-Hunt weak `(2,2)` maximal
inequality for the Carleson maximal operator; everything else -- the density/approximation
argument by trigonometric polynomials and the passage from the maximal inequality to almost
everywhere convergence -- is proved here from scratch.

Proved unconditionally (no hypothesis) in this file:

* `Math2.tendsto_eLpNorm_partialFourierSum` : `L²` convergence of the partial Fourier sums;
* `Math2.exists_subseq_ae_tendsto_partialFourierSum` : almost everywhere convergence of a
  subsequence of the partial Fourier sums.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory AddCircle Filter Topology

noncomputable section

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle 1 → ℂ`. -/
def partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

/-- The Carleson maximal operator: the pointwise supremum of the moduli of the partial sums
of the Fourier series of `f`. -/
def carlesonOperator (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖partialFourierSum f N x‖ₑ

/-- The weak `(2,2)` bound for the Carleson maximal operator, with constant `C`. This is the
key intermediate result in the proof of Carleson's theorem (the Carleson–Hunt inequality). -/
def CarlesonWeakL2 (C : ℝ≥0∞) : Prop :=
  ∀ g : AddCircle (1 : ℝ) → ℂ, MemLp g 2 haarAddCircle → ∀ lam : ℝ≥0∞, lam ≠ 0 →
    haarAddCircle {x | lam < carlesonOperator g x} ≤
      C * eLpNorm g 2 haarAddCircle ^ 2 / lam ^ 2

/-- Auxiliary quantity: the `limsup` of the distance from the partial sums to `f`. -/
def divergenceLimsup (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ℝ≥0∞ :=
  limsup (fun N : ℕ => ‖partialFourierSum f N x - f x‖ₑ) atTop

section Basic

variable {f g : AddCircle (1 : ℝ) → ℂ}

/-- Each partial Fourier sum is a continuous function. -/
theorem continuous_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) :
    Continuous (partialFourierSum f N) :=
  continuous_finset_sum _ fun n _ => continuous_const.mul (map_continuous (fourier n))

/-- Each partial Fourier sum lies in `Lᵖ`. -/
theorem memLp_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) {p : ℝ≥0∞} :
    MemLp (partialFourierSum f N) p haarAddCircle :=
  (continuous_partialFourierSum f N).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Each partial Fourier sum is integrable. -/
theorem integrable_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) :
    Integrable (partialFourierSum f N) haarAddCircle :=
  (memLp_partialFourierSum f N (p := 1)).integrable le_rfl

/-- The Fourier coefficients of a partial Fourier sum: they agree with those of `f` in the
range of summation and vanish outside it. -/
theorem fourierCoeff_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (m : ℤ) :
    fourierCoeff (partialFourierSum f N) m =
      if m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then fourierCoeff f m else 0 := by
  have h : partialFourierSum f N
      = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (fun x => fourierCoeff f n * fourier n x) := by
    funext x; simp [partialFourierSum]
  rw [h, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun n _ => by
      rw [fourierCoeff.const_mul (fun x => fourier n x) (fourierCoeff f n) m,
        show (fun x => (fourier n) x) = ⇑(fourier (T := (1 : ℝ)) n) from rfl,
        fourierCoeff_fourier n])]
    simp [Pi.single_apply, mul_ite]
  · intro n _
    exact ((map_continuous (fourier n)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 1)).integrable le_rfl |>.const_mul _

/-- Partial sums reproduce trigonometric polynomials: the `M`-th partial sum of the `N`-th
partial sum of `f` is the `N`-th partial sum of `f`, provided `N ≤ M`. -/
theorem partialFourierSum_partialFourierSum (f : AddCircle (1 : ℝ) → ℂ) {N M : ℕ} (h : N ≤ M) :
    partialFourierSum (partialFourierSum f N) M = partialFourierSum f N := by
  funext x
  show ∑ m ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), fourierCoeff (partialFourierSum f N) m * fourier m x
      = partialFourierSum f N x
  simp only [fourierCoeff_partialFourierSum, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.Icc_subset_Icc
    (by exact_mod_cast neg_le_neg (Nat.cast_le.mpr h)) (by exact_mod_cast h))]
  rfl

/-- Additivity of Fourier coefficients under subtraction. -/
theorem fourierCoeff_sub (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle)
    (n : ℤ) : fourierCoeff (fun y => f y - g y) n = fourierCoeff f n - fourierCoeff g n := by
  have h1 : (fun y => f y - g y) = f + (fun y => (-1 : ℂ) * g y) := by
    funext y; simp [sub_eq_add_neg]
  have h2 : Integrable (fun y => (-1 : ℂ) * g y) haarAddCircle := hg.const_mul _
  rw [h1, fourierCoeff.add hf h2, Pi.add_apply, fourierCoeff.const_mul g (-1) n]
  ring

/-- Linearity of the partial sums with respect to `f`. -/
theorem partialFourierSum_sub (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle)
    (N : ℕ) (x : AddCircle (1 : ℝ)) :
    partialFourierSum (fun y => f y - g y) N x =
      partialFourierSum f N x - partialFourierSum g N x := by
  simp only [partialFourierSum, fourierCoeff_sub hf hg, sub_mul, Finset.sum_sub_distrib]

/-- The coercion of a finite linear combination of the `L²` Fourier monomials is almost
everywhere the corresponding trigonometric polynomial. -/
theorem coeFn_trigPoly (c : ℤ → ℂ) (s : Finset ℤ) :
    ⇑(∑ i ∈ s, c i • (fourierLp (T := (1 : ℝ)) 2 i)) =ᵐ[haarAddCircle]
      fun x => ∑ i ∈ s, c i * fourier i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 (haarAddCircle (T := (1 : ℝ)))
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (c a • (fourierLp (T := (1 : ℝ)) 2 a))
          (∑ i ∈ s, c i • fourierLp 2 i),
        Lp.coeFn_smul (c a) (fourierLp (T := (1 : ℝ)) 2 a), coeFn_fourierLp (T := (1 : ℝ)) 2 a, ih]
        with x hx hsm hfl hx2
      rw [Finset.sum_insert ha, hx, Pi.add_apply, hsm, hx2, Finset.sum_insert ha, Pi.smul_apply,
        hfl, smul_eq_mul]

/-- The `L²` approximation property: the partial Fourier sums eventually approximate an `L²`
function to within any prescribed accuracy in the `L²` norm.  (This is the classical
Riesz–Fischer statement, which does *not* need Carleson's theorem.) -/
theorem eventually_eLpNorm_partialFourierSum_lt (hf : MemLp f 2 haarAddCircle) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, eLpNorm (fun x => f x - partialFourierSum f N x) 2 haarAddCircle < ε := by
  classical
  obtain ⟨e, he, hlt⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e < ε := by
    rcases eq_or_ne ε ∞ with rfl | h
    · exact ⟨1, one_pos, by simp⟩
    · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε.ne' h; linarith, ?_⟩
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal h]
      simpa using ENNReal.half_lt_self hε.ne' h
  set F : Lp ℂ 2 (haarAddCircle (T := (1 : ℝ))) := hf.toLp f with hF
  have hcoeff : ∀ i, fourierCoeff (⇑F) i = fourierCoeff f i := fun i =>
    congrFun (fourierCoeff_congr_ae (hf.coeFn_toLp)) i
  have hs := hasSum_fourier_series_L2 F
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hs e he)
  filter_upwards [Filter.eventually_ge_atTop (s₀.sup Int.natAbs)] with N hNge
  have hsub : s₀ ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro i hi
    have hi' : i.natAbs ≤ s₀.sup Int.natAbs := Finset.le_sup hi
    simp only [Finset.mem_Icc]; omega
  have hball := hs₀ (Finset.Icc (-(N : ℤ)) (N : ℤ)) hsub
  set G : Lp ℂ 2 (haarAddCircle (T := (1 : ℝ))) :=
    ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (⇑F) i • fourierLp 2 i with hG
  have hGco : ⇑G =ᵐ[haarAddCircle] partialFourierSum f N := by
    filter_upwards [coeFn_trigPoly (fun i => fourierCoeff (⇑F) i)
      (Finset.Icc (-(N : ℤ)) (N : ℤ))] with x hx
    rw [hG, hx]
    simp only [partialFourierSum, hcoeff]
  have hae : (fun x => f x - partialFourierSum f N x) =ᵐ[haarAddCircle] ⇑(F - G) := by
    filter_upwards [hf.coeFn_toLp, hGco, Lp.coeFn_sub F G] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  rw [eLpNorm_congr_ae hae]
  have hfin : eLpNorm (⇑(F - G)) 2 haarAddCircle ≠ ∞ := Lp.eLpNorm_ne_top _
  have hnorm : ‖F - G‖ < e := by rw [← dist_eq_norm, dist_comm]; exact hball
  calc eLpNorm (⇑(F - G)) 2 haarAddCircle
      = ENNReal.ofReal ‖F - G‖ := by rw [Lp.norm_def, ENNReal.ofReal_toReal hfin]
    _ < ENNReal.ofReal e := (ENNReal.ofReal_lt_ofReal_iff he).mpr hnorm
    _ < ε := hlt

/-- There is a partial Fourier sum approximating `f` to within any prescribed `L²` accuracy. -/
theorem exists_eLpNorm_partialFourierSum_lt (hf : MemLp f 2 haarAddCircle) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ N : ℕ, eLpNorm (fun x => f x - partialFourierSum f N x) 2 haarAddCircle < ε :=
  (eventually_eLpNorm_partialFourierSum_lt hf hε).exists

/-- **`L²` convergence of Fourier series** (unconditional): the partial Fourier sums of a
square-integrable function converge to it in the `L²` norm. -/
theorem tendsto_eLpNorm_partialFourierSum (hf : MemLp f 2 haarAddCircle) :
    Tendsto (fun N : ℕ => eLpNorm (fun x => f x - partialFourierSum f N x) 2 haarAddCircle)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [eventually_eLpNorm_partialFourierSum_lt hf hε] with N hN using hN.le

/-- **Almost everywhere convergence along a subsequence** (unconditional): for a square-integrable
function there is a subsequence of the partial Fourier sums converging to it almost everywhere.
This is much weaker than Carleson's theorem, which asserts convergence of the whole sequence. -/
theorem exists_subseq_ae_tendsto_partialFourierSum (hf : MemLp f 2 haarAddCircle) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂haarAddCircle, Tendsto (fun i => partialFourierSum f (ns i) x) atTop (𝓝 (f x)) := by
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable (partialFourierSum f N) haarAddCircle := fun N =>
    (continuous_partialFourierSum f N).aestronglyMeasurable
  have htend : Tendsto (fun N : ℕ => eLpNorm (partialFourierSum f N - f) 2 haarAddCircle)
      atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partialFourierSum hf
    refine h.congr fun N => ?_
    rw [← eLpNorm_neg]
    congr 1
    funext x
    simp
  exact (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hmeas
    hf.aestronglyMeasurable htend).exists_seq_tendsto_ae

end Basic

/-- Pointwise, each partial sum is dominated by the Carleson maximal operator. -/
theorem enorm_partialFourierSum_le_carlesonOperator (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) : ‖partialFourierSum f N x‖ₑ ≤ carlesonOperator f x :=
  le_iSup (fun N : ℕ => ‖partialFourierSum f N x‖ₑ) N

/-- Chebyshev's inequality in the form we need. -/
theorem meas_lt_enorm_le (g : AddCircle (1 : ℝ) → ℂ) (hg : MemLp g 2 haarAddCircle)
    {lam : ℝ≥0∞} (hlam : lam ≠ 0) :
    haarAddCircle {x | lam < ‖g x‖ₑ} ≤ eLpNorm g 2 haarAddCircle ^ 2 / lam ^ 2 := by
  rcases eq_or_ne lam ∞ with rfl | hlamtop
  · have h : {x : AddCircle (1 : ℝ) | (∞ : ℝ≥0∞) < ‖g x‖ₑ} = ∅ := by ext x; simp
    rw [h]
    simp
  have hmono : haarAddCircle {x : AddCircle (1 : ℝ) | lam < ‖g x‖ₑ}
      ≤ haarAddCircle {x : AddCircle (1 : ℝ) | lam ≤ ‖g x‖ₑ} := by
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact hx.le
  refine hmono.trans ?_
  have key := mul_meas_ge_le_pow_eLpNorm' (haarAddCircle (T := (1 : ℝ))) (p := 2)
    (by norm_num) (by norm_num) hg.aestronglyMeasurable lam
  simp only [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num] at key
  rw [ENNReal.rpow_two, ENNReal.rpow_two] at key
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness)), mul_comm]
  exact key

/-- The main estimate: assuming the weak `(2,2)` bound for the Carleson operator, the measure of
the set where the Fourier partial sums fail to converge to `f` by more than `lam` is bounded by a
quantity that can be made arbitrarily small by taking `ε` small. -/
theorem meas_divergenceLimsup_le {C : ℝ≥0∞} (hbound : CarlesonWeakL2 C)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) {lam : ℝ≥0∞} (hlam : lam ≠ 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    haarAddCircle {x | lam < divergenceLimsup f x} ≤ (C + 1) * ε ^ 2 / (lam / 2) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_eLpNorm_partialFourierSum_lt hf hε
  set P := partialFourierSum f N₀ with hP
  set g : AddCircle (1 : ℝ) → ℂ := fun x => f x - P x with hg
  have hfint : Integrable f haarAddCircle := hf.integrable (by norm_num)
  have hPint : Integrable P haarAddCircle := integrable_partialFourierSum f N₀
  have hgmem : MemLp g 2 haarAddCircle := hf.sub (memLp_partialFourierSum f N₀)
  have hptwise : ∀ x, divergenceLimsup f x ≤ carlesonOperator g x + ‖g x‖ₑ := by
    intro x
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have h1 : partialFourierSum g N x = partialFourierSum f N x - P x := by
      rw [hg, partialFourierSum_sub hfint hPint N x, hP,
        partialFourierSum_partialFourierSum f hN]
    have h2 : partialFourierSum f N x - f x = partialFourierSum g N x - g x := by
      rw [h1, hg]; ring
    calc ‖partialFourierSum f N x - f x‖ₑ = ‖partialFourierSum g N x - g x‖ₑ := by rw [h2]
      _ ≤ ‖partialFourierSum g N x‖ₑ + ‖g x‖ₑ := enorm_sub_le
      _ ≤ carlesonOperator g x + ‖g x‖ₑ := by
          gcongr
          exact enorm_partialFourierSum_le_carlesonOperator g N x
  have hsubset : {x | lam < divergenceLimsup f x} ⊆
      {x | lam / 2 < carlesonOperator g x} ∪ {x | lam / 2 < ‖g x‖ₑ} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
    have hle := (hptwise x).trans (add_le_add hcon.1 hcon.2)
    rw [ENNReal.add_halves] at hle
    exact absurd (lt_of_lt_of_le hx hle) (lt_irrefl _)
  have hhalf : lam / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hlam]
  calc haarAddCircle {x | lam < divergenceLimsup f x}
      ≤ haarAddCircle ({x | lam / 2 < carlesonOperator g x} ∪ {x | lam / 2 < ‖g x‖ₑ}) :=
        measure_mono hsubset
    _ ≤ haarAddCircle {x | lam / 2 < carlesonOperator g x}
          + haarAddCircle {x | lam / 2 < ‖g x‖ₑ} := measure_union_le _ _
    _ ≤ C * eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2
          + eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2 :=
        add_le_add (hbound g hgmem (lam / 2) hhalf) (meas_lt_enorm_le g hgmem hhalf)
    _ = (C + 1) * eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2 := by
        rw [ENNReal.div_add_div_same, add_mul, one_mul]
    _ ≤ (C + 1) * ε ^ 2 / (lam / 2) ^ 2 := by gcongr

/-- Consequently, for each fixed threshold the exceptional set is null. -/
theorem meas_divergenceLimsup_eq_zero {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : CarlesonWeakL2 C)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) {lam : ℝ≥0∞} (hlam : lam ≠ 0) :
    haarAddCircle {x | lam < divergenceLimsup f x} = 0 := by
  set L : ℝ≥0∞ := (lam / 2) ^ 2 with hL
  have hLne : L ≠ 0 := by
    have h : lam / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hlam]
    simp [hL, h]
  set K : ℝ≥0∞ := (C + 1) * L⁻¹ with hK
  have hKne : K ≠ ∞ := by
    apply ENNReal.mul_ne_top (by finiteness)
    simpa using hLne
  have hbdd : ∀ n : ℕ, 1 ≤ n →
      haarAddCircle {x | lam < divergenceLimsup f x} ≤ K * (n : ℝ≥0∞)⁻¹ := by
    intro n hn
    have hεpos : (0 : ℝ≥0∞) < (n : ℝ≥0∞)⁻¹ := by simp [ENNReal.inv_pos]
    refine (meas_divergenceLimsup_le hbound hf hlam hεpos).trans ?_
    have hle : ((n : ℝ≥0∞)⁻¹) ^ 2 ≤ (n : ℝ≥0∞)⁻¹ := by
      have h1 : (n : ℝ≥0∞)⁻¹ ≤ 1 := by
        rw [ENNReal.inv_le_one]; exact_mod_cast hn
      calc ((n : ℝ≥0∞)⁻¹) ^ 2 = (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := sq _
        _ ≤ (n : ℝ≥0∞)⁻¹ * 1 := by gcongr
        _ = (n : ℝ≥0∞)⁻¹ := mul_one _
    calc (C + 1) * ((n : ℝ≥0∞)⁻¹) ^ 2 / L = K * ((n : ℝ≥0∞)⁻¹) ^ 2 := by
          rw [hK, ENNReal.div_eq_inv_mul]; ring
      _ ≤ K * (n : ℝ≥0∞)⁻¹ := by gcongr
  have htend : Tendsto (fun n : ℕ => K * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := K) (b := (0 : ℝ≥0∞))
      ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hKne)
  refine le_antisymm (ge_of_tendsto htend ?_) (zero_le _)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hbdd n hn

/-- If the `limsup` of the distances vanishes at `x`, the Fourier series converges at `x`. -/
theorem tendsto_of_divergenceLimsup_eq_zero {f : AddCircle (1 : ℝ) → ℂ} {x : AddCircle (1 : ℝ)}
    (hx : divergenceLimsup f x = 0) :
    Tendsto (fun N => partialFourierSum f N x) atTop (𝓝 (f x)) := by
  have h1 : Tendsto (fun N => ‖partialFourierSum f N x - f x‖ₑ) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le (a := (0 : ℝ≥0∞)) bot_le (le_of_eq hx)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp h1
  simpa [Function.comp] using h2

/-- **Carleson's theorem.**  The Fourier series of a square-integrable function on the circle
converges to it almost everywhere.

The proof is conditional on the key intermediate result `CarlesonWeakL2 C`, the Carleson–Hunt
weak `(2,2)` maximal inequality for the Carleson operator, which is supplied as a hypothesis. -/
theorem carleson {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : CarlesonWeakL2 C)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle) :
    ∀ᵐ x ∂haarAddCircle, Tendsto (fun N => partialFourierSum f N x) atTop (𝓝 (f x)) := by
  have hzero : ∀ k : ℕ,
      haarAddCircle {x | ((k : ℝ≥0∞) + 1)⁻¹ < divergenceLimsup f x} = 0 := by
    intro k
    exact meas_divergenceLimsup_eq_zero hC hbound hf (by simp)
  have hset : {x | divergenceLimsup f x ≠ 0}
      = ⋃ k : ℕ, {x | ((k : ℝ≥0∞) + 1)⁻¹ < divergenceLimsup f x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx
      exact ⟨k, lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ k)) hk⟩
    · rintro ⟨k, hk⟩
      exact (lt_of_le_of_lt (zero_le _) hk).ne'
  have hae : ∀ᵐ x ∂haarAddCircle, divergenceLimsup f x = 0 := by
    rw [ae_iff, hset]
    exact measure_iUnion_null hzero
  filter_upwards [hae] with x hx
  exact tendsto_of_divergenceLimsup_eq_zero hx

end

end Math2

