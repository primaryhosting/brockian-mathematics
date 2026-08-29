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

import Mathlib

/-!
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/
def shiftedRange (T : H →ₗ.[ℂ] H) (z : ℂ) : Set H :=
  Set.range fun x : T.domain => (T x + z • (x : H))

omit [CompleteSpace H] in
theorem mem_shiftedRange {T : H →ₗ.[ℂ] H} {z : ℂ} (x : T.domain) :
    T x + z • (x : H) ∈ shiftedRange T z := ⟨x, rfl⟩

omit [CompleteSpace H] in
/-- A vector orthogonal to a dense set vanishes. -/
theorem eq_zero_of_dense_inner_eq_zero {s : Set H} (hs : Dense s) {y : H}
    (h : ∀ v ∈ s, ⟪y, v⟫ = 0) : y = 0 := by
  have hcont : Continuous fun w : H => ⟪y, w⟫ := (innerSL ℂ y).continuous
  have hall : ∀ w : H, ⟪y, w⟫ = 0 := by
    have : (fun w : H => ⟪y, w⟫) = fun _ : H => (0 : ℂ) :=
      hcont.ext_on hs continuous_const h
    exact fun w => congrFun this w
  simpa using hall y

/-- The adjoint is antitone. -/
theorem adjoint_le_adjoint {T S : H →ₗ.[ℂ] H} (hT : Dense (T.domain : Set H)) (h : T ≤ S) :
    S† ≤ T† := by
  have hS : Dense (S.domain : Set H) := Dense.mono (fun _ hx => h.1 hx) hT
  refine LinearPMap.IsFormalAdjoint.le_adjoint hT ?_
  intro x y
  have hx : (x : H) ∈ S.domain := h.1 x.2
  have hTx : T x = S ⟨(x : H), hx⟩ := h.2 rfl
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := S) hS y ⟨(x : H), hx⟩
  rw [hTx, ← inner_conj_symm, ← inner_conj_symm ((x : H))]
  simp only [hfa]

omit [CompleteSpace H] in
/-- For a symmetric operator `A` we have `‖x‖ ≤ ‖A x + i x‖`. -/
theorem norm_le_norm_add_I_smul {A : H →ₗ.[ℂ] H} (hsymm : A.IsFormalAdjoint A) (x : A.domain) :
    ‖(x : H)‖ ≤ ‖A x + Complex.I • (x : H)‖ := by
  have hre : (⟪A x, (x : H)⟫ : ℂ) = ⟪(x : H), A x⟫ := hsymm x x
  have h2 : (⟪A x, (x : H)⟫ : ℂ).im = 0 := by
    have h1 : (starRingEnd ℂ) (⟪A x, (x : H)⟫) = (⟪A x, (x : H)⟫ : ℂ) := by
      rw [inner_conj_symm]; exact hre.symm
    have := congrArg Complex.im h1
    simp only [Complex.conj_im] at this
    linarith
  have hzero : Complex.re (⟪A x, Complex.I • (x : H)⟫ : ℂ) = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, h2]
  have hsq : ‖A x + Complex.I • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
    rw [@norm_add_sq ℂ]
    simp only [hzero, norm_smul, Complex.norm_I, one_mul, RCLike.re_to_complex]
    ring
  have h1 : ‖(x : H)‖ ^ 2 ≤ ‖A x + Complex.I • (x : H)‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg ‖A x‖]
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (A x + Complex.I • (x : H)), norm_nonneg ((x : H))]

/-- If `A` is closed, symmetric and the range of `A + i` is dense, then `A + i` is surjective. -/
theorem surjective_add_I_of_isClosed {A : H →ₗ.[ℂ] H} (hclosed : A.IsClosed)
    (hsymm : A.IsFormalAdjoint A) (hdense : Dense (shiftedRange A Complex.I)) (v : H) :
    ∃ w : A.domain, A w + Complex.I • (w : H) = v := by
  classical
  have hclosedRange : IsClosed (shiftedRange A Complex.I) := by
    apply IsSeqClosed.isClosed
    intro f p hf hfp
    choose w hw using hf
    -- the sequence `w` is Cauchy
    have hfCauchy : CauchySeq f := hfp.cauchySeq
    have hwCauchy : CauchySeq fun n => ((w n : H)) := by
      rw [Metric.cauchySeq_iff] at hfCauchy ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hfCauchy ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      have key : ‖((w m : H)) - ((w n : H))‖ ≤ ‖f m - f n‖ := by
        have hsub : f m - f n = A (w m - w n) + Complex.I • ((w m : H) - (w n : H)) := by
          rw [← hw m, ← hw n, A.map_sub]
          simp only [smul_sub]
          abel
        have := norm_le_norm_add_I_smul hsymm (w m - w n)
        simpa [hsub] using this
      calc dist ((w m : H)) ((w n : H)) = ‖((w m : H)) - ((w n : H))‖ := dist_eq_norm _ _
        _ ≤ ‖f m - f n‖ := key
        _ = dist (f m) (f n) := (dist_eq_norm _ _).symm
        _ < ε := hN m hm n hn
    obtain ⟨w₀, hw₀⟩ := cauchySeq_tendsto_of_complete hwCauchy
    have hAw : Tendsto (fun n => A (w n)) atTop (𝓝 (p - Complex.I • w₀)) := by
      have h1 : Tendsto (fun n => f n - Complex.I • ((w n : H))) atTop
          (𝓝 (p - Complex.I • w₀)) := hfp.sub (hw₀.const_smul Complex.I)
      refine h1.congr (fun n => ?_)
      rw [← hw n]
      simp
    have hmem : (w₀, p - Complex.I • w₀) ∈ A.graph := by
      refine hclosed.mem_of_tendsto (hw₀.prodMk_nhds hAw) ?_
      filter_upwards with n
      exact A.mem_graph (w n)
    rw [LinearPMap.mem_graph_iff] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hy1 : (y : H) = w₀ := hy.1
    have hy2 : A y = p - Complex.I • w₀ := hy.2
    refine ⟨y, ?_⟩
    show A y + Complex.I • (y : H) = p
    rw [hy2, hy1]
    abel
  have : shiftedRange A Complex.I = Set.univ := by
    rw [← hclosedRange.closure_eq, hdense.closure_eq]
  have hv : v ∈ shiftedRange A Complex.I := by rw [this]; trivial
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, hw⟩

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
whose ranges `T + i` and `T - i` are dense has self-adjoint adjoint; equivalently, `T` is
essentially self-adjoint. -/
theorem isSelfAdjoint_adjoint_of_dense_shiftedRange {T : H →ₗ.[ℂ] H}
    (hdense : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (shiftedRange T Complex.I))
    (hminus : Dense (shiftedRange T (-Complex.I))) : IsSelfAdjoint (T†) := by
  classical
  have hTT : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hdense hsymm
  have hdense' : Dense ((T†).domain : Set H) := Dense.mono (fun _ hx => hTT.1 hx) hdense
  -- `A := T††`
  set A : H →ₗ.[ℂ] H := (T†)† with hA
  have hAle : A ≤ T† := adjoint_le_adjoint hdense hTT
  have hTA : T ≤ A :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense' (LinearPMap.adjoint_isFormalAdjoint hdense)
  have hAdense : Dense ((A.domain : Set H)) := Dense.mono (fun _ hx => hTA.1 hx) hdense
  have hAclosed : A.IsClosed := LinearPMap.adjoint_isClosed hdense'
  have hAsymm : A.IsFormalAdjoint A := by
    intro x y
    have hy : (y : H) ∈ (T†).domain := hAle.1 y.2
    have hTy : A y = T† ⟨(y : H), hy⟩ := hAle.2 rfl
    have := LinearPMap.adjoint_isFormalAdjoint (T := T†) hdense' x ⟨(y : H), hy⟩
    rw [hTy]
    exact this
  -- the range of `A + i` is dense, since it contains the range of `T + i`
  have hAplus : Dense (shiftedRange A Complex.I) := by
    refine Dense.mono ?_ hplus
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨(x : H), hTA.1 x.2⟩, ?_⟩
    show A ⟨(x : H), hTA.1 x.2⟩ + Complex.I • (x : H) = T x + Complex.I • (x : H)
    rw [hTA.2 (x := x) (y := ⟨(x : H), hTA.1 x.2⟩) rfl]
  -- hence `A + i` is surjective
  have hsurj := surjective_add_I_of_isClosed hAclosed hAsymm hAplus
  -- now show `T† ≤ A`
  have hle : T† ≤ A := by
    have hdom : (T†).domain ≤ A.domain := by
      intro y hy
      obtain ⟨w, hw⟩ := hsurj (T† ⟨y, hy⟩ + Complex.I • y)
      set y' : H := y - (w : H) with hy'
      have hwT : (w : H) ∈ (T†).domain := hAle.1 w.2
      have hy'mem : y' ∈ (T†).domain := Submodule.sub_mem _ hy hwT
      have hTw : T† ⟨(w : H), hwT⟩ = A w := (hAle.2 rfl).symm
      have hTy' : T† ⟨y', hy'mem⟩ = -(Complex.I • y') := by
        have hsub : (⟨y', hy'mem⟩ : (T†).domain)
            = (⟨y, hy⟩ : (T†).domain) - ⟨(w : H), hwT⟩ := by
          apply Subtype.ext; simp [hy']
        rw [hsub, (T†).map_sub, hTw]
        have : A w = T† ⟨y, hy⟩ + Complex.I • y - Complex.I • (w : H) := by
          rw [← hw]; abel
        rw [this, hy']
        simp only [smul_sub]
        abel
      -- `y'` is orthogonal to the range of `T - i`
      have horth : ∀ v ∈ shiftedRange T (-Complex.I), ⟪y', v⟫ = 0 := by
        rintro _ ⟨x, rfl⟩
        have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hdense ⟨y', hy'mem⟩ x
        have h1 : (⟪y', T x⟫ : ℂ) = ⟪-(Complex.I • y'), (x : H)⟫ := by
          rw [← hTy']
          exact hfa.symm
        rw [inner_add_right, h1]
        rw [inner_smul_right, inner_neg_left, inner_smul_left]
        simp [Complex.conj_I]
      have hy'zero : y' = 0 := eq_zero_of_dense_inner_eq_zero hminus horth
      have : y = (w : H) := by
        have := sub_eq_zero.mp hy'zero
        exact this
      rw [this]
      exact w.2
    refine ⟨hdom, ?_⟩
    rintro ⟨y, hy⟩ ⟨y2, hy2⟩ (hyy : y = y2)
    subst hyy
    -- values agree
    obtain ⟨w, hw⟩ := hsurj (T† ⟨y, hy⟩ + Complex.I • y)
    have hwT : (w : H) ∈ (T†).domain := hAle.1 w.2
    have hTw : T† ⟨(w : H), hwT⟩ = A w := (hAle.2 rfl).symm
    have hy'mem : y - (w : H) ∈ (T†).domain := Submodule.sub_mem _ hy hwT
    have hTy' : T† ⟨y - (w : H), hy'mem⟩ = -(Complex.I • (y - (w : H))) := by
      have hsub : (⟨y - (w : H), hy'mem⟩ : (T†).domain)
          = (⟨y, hy⟩ : (T†).domain) - ⟨(w : H), hwT⟩ := by
        apply Subtype.ext; simp
      rw [hsub, (T†).map_sub, hTw]
      have : A w = T† ⟨y, hy⟩ + Complex.I • y - Complex.I • (w : H) := by
        rw [← hw]; abel
      rw [this]
      simp only [smul_sub]
      abel
    have horth : ∀ v ∈ shiftedRange T (-Complex.I), ⟪y - (w : H), v⟫ = 0 := by
      rintro _ ⟨x, rfl⟩
      have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hdense ⟨y - (w : H), hy'mem⟩ x
      have h1 : (⟪y - (w : H), T x⟫ : ℂ) = ⟪-(Complex.I • (y - (w : H))), (x : H)⟫ := by
        rw [← hTy']
        exact hfa.symm
      rw [inner_add_right, h1, inner_smul_right, inner_neg_left, inner_smul_left]
      simp [Complex.conj_I]
    have hyw : y = (w : H) := sub_eq_zero.mp (eq_zero_of_dense_inner_eq_zero hminus horth)
    have : T† ⟨y, hy⟩ = A w := by
      have : (⟨y, hy⟩ : (T†).domain) = ⟨(w : H), hwT⟩ := Subtype.ext hyw
      rw [this, hTw]
    rw [this]
    have : (⟨y, hy2⟩ : A.domain) = w := Subtype.ext hyw
    rw [this]
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAle hle

end Brockian.Weyl

import Mathlib

/-!
# Resolvents of the one-dimensional Laplacian on Schwartz space

For every Schwartz function `h` on `ℝ` and every non-real `z`, the equation
`-u'' + z u = h` has a Schwartz solution `u`, obtained by dividing the Fourier transform of `h`
by the symbol `4 π² ξ² + z`.

Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex SchwartzMap Real
open scoped Nat ContDiff FourierTransform SchwartzMap

namespace Brockian.Weyl

/-- A one-dimensional function all of whose iterated derivatives are bounded has temperate
growth. -/
theorem hasTemperateGrowth_of_bounded_iteratedDeriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∃ C : ℝ, ∀ t : ℝ, ‖iteratedDeriv n f t‖ ≤ C) :
    Function.HasTemperateGrowth f := by
  refine ⟨hf, fun n => ?_⟩
  obtain ⟨C, hC⟩ := h n
  refine ⟨0, C, fun t => ?_⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC t

/-- The iterated derivatives of `t ↦ (t + z)⁻¹` on the real line. -/
theorem iteratedDeriv_inv_ofReal_add {z : ℂ} (hz : ∀ t : ℝ, ((t : ℂ) + z) ≠ 0) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ((t : ℂ) + z)⁻¹)
      = fun t : ℝ => (-1) ^ n * (n ! : ℂ) / (((t : ℂ) + z) ^ (n + 1)) := by
  induction n with
  | zero => ext t; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext t
    have h1 : HasDerivAt (fun t : ℝ => ((t : ℂ) + z)) 1 t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const z
    have h2 : HasDerivAt (fun t : ℝ => ((t : ℂ) + z) ^ (n + 1))
        (((n : ℂ) + 1) * ((t : ℂ) + z) ^ n * 1) t := by
      simpa using h1.pow (n + 1)
    have hne : ((t : ℂ) + z) ^ (n + 1) ≠ 0 := pow_ne_zero _ (hz t)
    have h3 : HasDerivAt (fun t : ℝ => ((-1 : ℂ) ^ n * (n ! : ℂ)) / (((t : ℂ) + z) ^ (n + 1)))
        ((0 * ((t : ℂ) + z) ^ (n + 1) -
            ((-1 : ℂ) ^ n * (n ! : ℂ)) * (((n : ℂ) + 1) * ((t : ℂ) + z) ^ n * 1))
          / (((t : ℂ) + z) ^ (n + 1)) ^ 2) t :=
      (hasDerivAt_const t ((-1 : ℂ) ^ n * (n ! : ℂ))).div h2 hne
    rw [h3.deriv]
    have hne0 := hz t
    field_simp
    push_cast [Nat.factorial_succ]
    ring

/-- For non-real `z`, the function `t ↦ (t + z)⁻¹` has temperate growth on `ℝ`. -/
theorem hasTemperateGrowth_inv_ofReal_add {z : ℂ} (hz : z.im ≠ 0) :
    Function.HasTemperateGrowth (fun t : ℝ => ((t : ℂ) + z)⁻¹) := by
  have hne : ∀ t : ℝ, ((t : ℂ) + z) ≠ 0 := by
    intro t hc
    apply hz
    have := congrArg Complex.im hc
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at this
    exact this
  have hlb : ∀ t : ℝ, |z.im| ≤ ‖(t : ℂ) + z‖ := by
    intro t
    have himeq : ((t : ℂ) + z).im = z.im := by simp
    calc |z.im| = |((t : ℂ) + z).im| := by rw [himeq]
      _ ≤ ‖(t : ℂ) + z‖ := Complex.abs_im_le_norm _
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  refine hasTemperateGrowth_of_bounded_iteratedDeriv
    (ContDiff.inv (Complex.ofRealCLM.contDiff.add contDiff_const) hne) (fun n => ?_)
  refine ⟨(n ! : ℝ) / |z.im| ^ (n + 1), fun t => ?_⟩
  rw [iteratedDeriv_inv_ofReal_add hne n]
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [Complex.norm_natCast]
  gcongr
  exact hlb t

/-- **Solvability of the resolvent equation on Schwartz space.**  For every non-real `z` and every
Schwartz function `h`, there is a Schwartz function `u` with `-u'' + z u = h`. -/
theorem exists_schwartz_neg_deriv_two_add_smul {z : ℂ} (hz : z.im ≠ 0) (h : 𝓢(ℝ, ℂ)) :
    ∃ u : 𝓢(ℝ, ℂ), -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) + z • u = h := by
  have hfd : ∀ (f : 𝓢(ℝ, ℂ)) (ξ : ℝ),
      (𝓕 (SchwartzMap.derivCLM ℂ ℂ f)) ξ = (2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ := by
    intro f ξ
    have hd : ⇑(SchwartzMap.derivCLM ℂ ℂ f) = deriv (⇑f) := by
      ext x; simp [SchwartzMap.derivCLM_apply]
    rw [SchwartzMap.fourier_coe, hd, Real.fourier_deriv f.integrable f.differentiable
      (by rw [← hd]; exact (SchwartzMap.derivCLM ℂ ℂ f).integrable)]
    simp [SchwartzMap.fourier_coe]
  set m : ℝ → ℂ := fun ξ => (((4 * Real.pi ^ 2 * ξ ^ 2 : ℝ) : ℂ) + z)⁻¹ with hm
  have hmtg : Function.HasTemperateGrowth m :=
    (hasTemperateGrowth_inv_ofReal_add hz).comp (by fun_prop)
  refine ⟨𝓕⁻ (SchwartzMap.smulLeftCLM ℂ m (𝓕 h)), ?_⟩
  set u : 𝓢(ℝ, ℂ) := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ m (𝓕 h)) with hu
  have hFu : 𝓕 u = SchwartzMap.smulLeftCLM ℂ m (𝓕 h) := FourierTransform.fourier_fourierInv_eq _
  have hinj : ∀ a b : 𝓢(ℝ, ℂ), 𝓕 a = 𝓕 b → a = b := by
    intro a b hab
    have ha : (𝓕⁻ (𝓕 a) : 𝓢(ℝ, ℂ)) = a := FourierTransform.fourierInv_fourier_eq a
    have hb : (𝓕⁻ (𝓕 b) : 𝓢(ℝ, ℂ)) = b := FourierTransform.fourierInv_fourier_eq b
    rw [← ha, ← hb, hab]
  apply hinj
  have hlin : 𝓕 (-(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u)) + z • u)
      = -(𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u))) + z • 𝓕 u := by
    show SchwartzMap.fourierTransformCLM ℂ _ = _
    rw [map_add, map_neg, map_smul]
    rfl
  rw [hlin]
  ext ξ
  have h1 : (𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ u))) ξ
      = (2 * Real.pi * Complex.I * ξ) * ((2 * Real.pi * Complex.I * ξ) * (𝓕 u) ξ) := by
    rw [hfd, hfd]
  have h2 : (𝓕 u) ξ = m ξ * (𝓕 h) ξ := by
    rw [hFu, SchwartzMap.smulLeftCLM_apply_apply hmtg]
    simp
  have hne : (((4 * Real.pi ^ 2 * ξ ^ 2 : ℝ) : ℂ) + z) ≠ 0 := by
    intro hc
    apply hz
    have := congrArg Complex.im hc
    rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at this
    exact this
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply, h1, h2, hm,
    smul_eq_mul]
  field_simp
  rw [Complex.I_sq]
  push_cast
  ring

end Brockian.Weyl

import Mathlib
import Brockian.Weyl.EssentialSelfAdjointness
import Brockian.Weyl.SchwartzResolvent

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Complex LinearPMap
open scoped SchwartzMap FourierTransform

namespace Brockian.Weyl.FreeLaplacian2

/-- The complex Hilbert space `L²(ℝ)`. -/
abbrev L2R : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The inclusion of the Schwartz space into `L²(ℝ)`. -/
noncomputable def schwartzToL2 : 𝓢(ℝ, ℂ) →L[ℂ] L2R := SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem schwartzToL2_apply (f : 𝓢(ℝ, ℂ)) : schwartzToL2 f = f.toLp 2 volume := rfl

theorem schwartzToL2_injective : Function.Injective (schwartzToL2.toLinearMap) :=
  SchwartzMap.injective_toLp 2 volume

/-- `-d²/dx²` acting on Schwartz functions. -/
noncomputable def freeLaplacianSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  -(SchwartzMap.derivCLM ℂ ℂ ∘L SchwartzMap.derivCLM ℂ ℂ)

theorem freeLaplacianSchwartz_apply (f : 𝓢(ℝ, ℂ)) :
    freeLaplacianSchwartz f = -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) := rfl

/-- The free Laplacian `-d²/dx²` on `L²(ℝ)`, as an unbounded operator whose domain is the space
of Schwartz functions. -/
noncomputable def freeLaplacian : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range schwartzToL2.toLinearMap
  toFun := (schwartzToL2.toLinearMap.comp freeLaplacianSchwartz.toLinearMap).comp
    (LinearEquiv.ofInjective schwartzToL2.toLinearMap schwartzToL2_injective).symm.toLinearMap

theorem freeLaplacian_domain :
    (freeLaplacian.domain : Set L2R) = Set.range (schwartzToL2 : 𝓢(ℝ, ℂ) → L2R) := by
  simp [freeLaplacian]

theorem mem_freeLaplacian_domain (f : 𝓢(ℝ, ℂ)) : (schwartzToL2 f) ∈ freeLaplacian.domain :=
  ⟨f, rfl⟩

@[simp]
theorem freeLaplacian_apply (f : 𝓢(ℝ, ℂ)) :
    freeLaplacian ⟨schwartzToL2 f, mem_freeLaplacian_domain f⟩
      = schwartzToL2 (freeLaplacianSchwartz f) := by
  have h : (⟨schwartzToL2 f, mem_freeLaplacian_domain f⟩ :
      (LinearMap.range schwartzToL2.toLinearMap)) =
      LinearEquiv.ofInjective schwartzToL2.toLinearMap schwartzToL2_injective f := rfl
  show ((schwartzToL2.toLinearMap.comp freeLaplacianSchwartz.toLinearMap).comp
    (LinearEquiv.ofInjective schwartzToL2.toLinearMap schwartzToL2_injective).symm.toLinearMap)
      ⟨schwartzToL2 f, mem_freeLaplacian_domain f⟩ = _
  rw [h]
  simp

/-- The Schwartz functions are dense in `L²(ℝ)`. -/
theorem dense_range_schwartzToL2 : Dense (Set.range (schwartzToL2 : 𝓢(ℝ, ℂ) → L2R)) := by
  have h : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (by simp)
  have hEq : ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ))
      = (schwartzToL2 : 𝓢(ℝ, ℂ) → L2R) := rfl
  rwa [hEq] at h

theorem dense_freeLaplacian_domain : Dense ((freeLaplacian.domain : Set L2R)) := by
  rw [freeLaplacian_domain]
  exact dense_range_schwartzToL2

/-- The `ℝ`-bilinear form `(a, b) ↦ conj a * b` on `ℂ`. -/
noncomputable def sesqMul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem sesqMul_apply (a b : ℂ) : sesqMul a b = (starRingEnd ℂ) a * b := rfl

/-- Integration by parts twice: `∫ conj u'' v = ∫ conj u v''` for Schwartz functions. -/
theorem integral_conj_deriv_two (u v : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, (starRingEnd ℂ) (deriv (deriv ⇑u) x) * v x
      = ∫ x : ℝ, (starRingEnd ℂ) (u x) * deriv (deriv ⇑v) x := by
  have hdu : ⇑(SchwartzMap.derivCLM ℂ ℂ u) = deriv ⇑u := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have hdv : ⇑(SchwartzMap.derivCLM ℂ ℂ v) = deriv ⇑v := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have step1 := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left u
    (SchwartzMap.derivCLM ℂ ℂ v) sesqMul
  have step2 := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left
    (SchwartzMap.derivCLM ℂ ℂ u) v sesqMul
  simp only [sesqMul_apply, hdu, hdv] at step1 step2
  rw [step2, ← step1]

theorem freeLaplacian_isFormalAdjoint : freeLaplacian.IsFormalAdjoint freeLaplacian := by
  intro x y
  obtain ⟨u, hu⟩ := x.2
  obtain ⟨v, hv⟩ := y.2
  have hx : x = ⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩ := Subtype.ext hu.symm
  have hy : y = ⟨schwartzToL2 v, mem_freeLaplacian_domain v⟩ := Subtype.ext hv.symm
  subst hx
  subst hy
  rw [freeLaplacian_apply, freeLaplacian_apply]
  show inner ℂ (schwartzToL2 (freeLaplacianSchwartz u)) (schwartzToL2 v)
    = inner ℂ (schwartzToL2 u) (schwartzToL2 (freeLaplacianSchwartz v))
  simp only [schwartzToL2_apply, SchwartzMap.inner_toL2_toL2_eq, freeLaplacianSchwartz_apply]
  have hdu : ⇑(SchwartzMap.derivCLM ℂ ℂ u) = deriv ⇑u := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have hdv : ⇑(SchwartzMap.derivCLM ℂ ℂ v) = deriv ⇑v := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have key := integral_conj_deriv_two u v
  simp only [RCLike.inner_apply, SchwartzMap.neg_apply, SchwartzMap.derivCLM_apply, hdu, hdv,
    map_neg, neg_mul, mul_neg, integral_neg, key]

/-- The range of `freeLaplacian + z` is dense for non-real `z`. -/
theorem dense_shiftedRange {z : ℂ} (hz : z.im ≠ 0) :
    Dense (Brockian.Weyl.shiftedRange freeLaplacian z) := by
  refine Dense.mono ?_ dense_range_schwartzToL2
  rintro _ ⟨h, rfl⟩
  obtain ⟨u, hu⟩ := Brockian.Weyl.exists_schwartz_neg_deriv_two_add_smul hz h
  refine ⟨⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩, ?_⟩
  show freeLaplacian ⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩ + z • (schwartzToL2 u)
    = schwartzToL2 h
  rw [freeLaplacian_apply, freeLaplacianSchwartz_apply, ← hu]
  simp

/-- **The free Laplacian on the Schwartz space is essentially self-adjoint.**

The operator `-d²/dx²` on `L²(ℝ)` with domain the Schwartz functions has a self-adjoint adjoint,
i.e. it is essentially self-adjoint.

The name records that the proof proceeds via the Fourier transform: the hypothesis about the
Fourier transform (solvability of `-u'' ± i u = h` on the Schwartz space) is discharged here,
so the statement is unconditional. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier : IsSelfAdjoint (freeLaplacian†) := by
  refine Brockian.Weyl.isSelfAdjoint_adjoint_of_dense_shiftedRange dense_freeLaplacian_domain
    freeLaplacian_isFormalAdjoint (dense_shiftedRange ?_) (dense_shiftedRange ?_) <;> simp

end Brockian.Weyl.FreeLaplacian2

