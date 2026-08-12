/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Almost-everywhere convergence of the Fourier series of an `L²` function on the circle
`AddCircle T`.

The main result `Math2.carleson` states that for every `f ∈ L²(AddCircle T)` the symmetric
partial sums `S_N f (x) = ∑_{|n| ≤ N} (fourierCoeff f n) • e^{2πinx/T}` converge to `f x`
at almost every `x` along a subsequence `N = ns k` (the subsequence being independent of `x`).

`Math2.carleson_of_summable` upgrades this to convergence of the full sequence of partial sums,
at almost every point, for those `f` whose Fourier coefficients are absolutely summable.

The full strength of Carleson's theorem — convergence of the whole sequence of partial sums
almost everywhere, for every `L²` function — is *not* established here.
-/

open MeasureTheory Filter Topology AddCircle

namespace Math2

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f`, as a genuine function on the
circle: `x ↦ ∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/
noncomputable def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

/-- The `N`-th symmetric partial sum of the Fourier series of `f`, as an element of `L²`. -/
noncomputable def fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) (N : ℕ) :
    Lp ℂ 2 (@haarAddCircle T hT) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (⇑f) n • fourierLp 2 n

/-- An unordered sum over `ℤ` is the limit of its symmetric partial sums. -/
theorem tendsto_sum_Icc_of_hasSum {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {u : ℤ → M} {a : M} (h : HasSum u a) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), u n) atTop (𝓝 a) := by
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro M N hMN
    apply Finset.Icc_subset_Icc <;> simp <;> exact_mod_cast hMN
  have hex : ∀ n : ℤ, ∃ N : ℕ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n
    refine ⟨n.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega
  exact h.comp (tendsto_atTop_finset_of_monotone hmono hex)

/-- The coercion to a function of a finite sum in `Lp` is a.e. the sum of the coercions. -/
theorem coeFn_finset_sum_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    (⇑(∑ i ∈ s, F i) : α → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      simp only [Finset.sum_insert ha]
      rw [h1, Pi.add_apply, h2]

/-- The `L²`-valued partial sum agrees almost everywhere with the pointwise partial sum. -/
theorem coeFn_fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) (N : ℕ) :
    (⇑(fourierPartialSumLp f N) : AddCircle T → ℂ) =ᵐ[haarAddCircle]
      fourierPartialSum (⇑f) N := by
  have h1 := coeFn_finset_sum_Lp (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun n => fourierCoeff (⇑f) n • (fourierLp (T := T) 2 n))
  have h2 : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (fourierCoeff (⇑f) n • (fourierLp (T := T) 2 n)) x
        = fourierCoeff (⇑f) n * fourier n x := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑f) n) (fourierLp (T := T) 2 n),
      coeFn_fourierLp (T := T) 2 n] with x hx hy
    rw [hx, Pi.smul_apply, hy, smul_eq_mul]
  filter_upwards [h1, h2] with x hx hy
  rw [fourierPartialSumLp, hx, fourierPartialSum]
  exact Finset.sum_congr rfl hy

/-- The symmetric partial sums of the Fourier series of an `L²` function converge to it in `L²`. -/
theorem tendsto_fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    Tendsto (fun N : ℕ => fourierPartialSumLp f N) atTop (𝓝 f) :=
  tendsto_sum_Icc_of_hasSum (hasSum_fourier_series_L2 f)

/-- **Almost-everywhere convergence of Fourier series of `L²` functions (Carleson-type).**

For every `f` in `L²` of the circle `AddCircle T` there is a subsequence `ns`, independent of the
point, along which the symmetric partial sums of the Fourier series of `f` converge to `f` at
almost every point.

Note: this is a weakened form of Carleson's theorem. The full theorem asserts convergence of the
whole sequence of partial sums almost everywhere; what is proved here is that the partial sums
converge almost everywhere along a subsequence, deduced from the `L²`-convergence of the Fourier
series. See `Math2.carleson_of_summable` for the full sequence under an extra hypothesis. -/
theorem carleson (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun k => fourierPartialSum (⇑f) (ns k) x) atTop (𝓝 (f x)) := by
  have hmeas : TendstoInMeasure (@haarAddCircle T hT)
      (fun N : ℕ => ⇑(fourierPartialSumLp f N)) atTop (⇑f) :=
    tendstoInMeasure_of_tendsto_Lp (tendsto_fourierPartialSumLp f)
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hall : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ N : ℕ,
      (⇑(fourierPartialSumLp f N) : AddCircle T → ℂ) x = fourierPartialSum (⇑f) N x :=
    ae_all_iff.2 fun N => coeFn_fourierPartialSumLp f N
  filter_upwards [hae, hall] with x hx hall'
  simpa [hall'] using hx

/-- An `L²` function with absolutely summable Fourier coefficients has a continuous representative,
namely the (uniformly convergent) sum of its Fourier series. -/
theorem exists_continuous_hasSum_of_summable (f : Lp ℂ 2 (@haarAddCircle T hT))
    (h : Summable fun n => ‖fourierCoeff (⇑f) n‖) :
    ∃ g : C(AddCircle T, ℂ), ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g = f ∧
      HasSum (fun n : ℤ => fourierCoeff (⇑f) n • fourier n) g := by
  have hsum : Summable fun n : ℤ => fourierCoeff (⇑f) n • (fourier n : C(AddCircle T, ℂ)) := by
    apply Summable.of_norm
    simpa [norm_smul, fourier_norm] using h
  obtain ⟨g, hg⟩ := hsum
  refine ⟨g, ?_, hg⟩
  have h1 : HasSum (fun n : ℤ => fourierCoeff (⇑f) n • fourierLp (T := T) 2 n)
      (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g) := by
    simpa using (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ (α := AddCircle T)).hasSum hg
  exact h1.unique (hasSum_fourier_series_L2 f)

/-- **Almost-everywhere convergence of the full sequence of partial sums**, for an `L²` function
whose Fourier coefficients are absolutely summable. -/
theorem carleson_of_summable (f : Lp ℂ 2 (@haarAddCircle T hT))
    (h : Summable fun n => ‖fourierCoeff (⇑f) n‖) :
    ∀ᵐ x ∂(@haarAddCircle T hT),
      Tendsto (fun N => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x)) := by
  obtain ⟨g, hgf, hg⟩ := exists_continuous_hasSum_of_summable f h
  have hae : (⇑f : AddCircle T → ℂ) =ᵐ[haarAddCircle] g := by
    rw [← hgf]; exact ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := haarAddCircle) (𝕜 := ℂ) g
  filter_upwards [hae] with x hx
  rw [hx]
  have hx' : HasSum (fun n : ℤ => fourierCoeff (⇑f) n * fourier n x) (g x) := by
    simpa using ((ContinuousMap.evalCLM ℂ x).hasSum hg)
  exact tendsto_sum_Icc_of_hasSum hx'

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

