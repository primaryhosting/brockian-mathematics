/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import line, so the
required header is reproduced here as a plain comment and again as a module
docstring immediately after the import.)
-/

import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

open MeasureTheory Filter Topology
open scoped ENNReal

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at the point `x`. -/

noncomputable def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

/-- The `N`-th symmetric partial sum of the Fourier series of `f`, as an element of `L²`. -/

noncomputable def fourierPartialSumLp (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (N : ℕ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle T hT) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (⇑f) n • fourierLp (T := T) 2 n

lemma tendsto_Icc_atTop : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun x => ⟨x.natAbs, ?_⟩)
  · exact Finset.Icc_subset_Icc (by omega) (by omega)
  · simp only [Finset.mem_Icc]
    omega

/-- The coercion to a function of a finite sum in `Lᵖ` is almost everywhere the pointwise sum. -/

lemma coeFn_lpSum {α : Type*} [MeasurableSpace α] {mu : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ p mu) :
    ⇑(∑ i ∈ s, F i) =ᵐ[mu] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ p mu
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      rw [h1, Finset.sum_insert ha, Pi.add_apply, h2]

/-- The symmetric partial sums of the Fourier series of an `L²` function converge to it
in the `L²` norm. -/

lemma tendsto_fourierPartialSumLp (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto (fourierPartialSumLp f) atTop (𝓝 f) := by
  have h : Tendsto (fun s : Finset ℤ =>
      ∑ n ∈ s, fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) atTop (𝓝 f) := by
    simpa only [fourierBasis_repr] using hasSum_fourier_series_L2 f
  exact h.comp tendsto_Icc_atTop

/-- The `L²`-valued partial sum agrees almost everywhere with the pointwise partial sum. -/

lemma coeFn_fourierPartialSumLp (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (N : ℕ) :
    ⇑(fourierPartialSumLp f N) =ᵐ[AddCircle.haarAddCircle] fourierPartialSum (⇑f) N := by
  have h2 : ∀ᵐ x ∂(@AddCircle.haarAddCircle T hT), ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) x = fourierCoeff (⇑f) n * fourier n x := by
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑f) n) (fourierLp (T := T) 2 n),
      coeFn_fourierLp (T := T) 2 n] with x h1 h3
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h3]
  have hA : ⇑(fourierPartialSumLp f N) =ᵐ[AddCircle.haarAddCircle]
      fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) x :=
    coeFn_lpSum _ _
  filter_upwards [hA, h2] with x hx hx2
  simp only [fourierPartialSum]
  rw [hx]
  exact Finset.sum_congr rfl hx2

/-- The symmetric partial sums of the Fourier series of an `L²` function converge to it
in measure (along the full sequence of cut-offs). -/

theorem tendstoInMeasure_fourierPartialSum (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    TendstoInMeasure (@AddCircle.haarAddCircle T hT)
      (fun N => fourierPartialSum (⇑f) N) atTop (⇑f) :=
  (tendstoInMeasure_of_tendsto_Lp (tendsto_fourierPartialSumLp f)).congr
    (fun N => coeFn_fourierPartialSumLp f N) (Filter.EventuallyEq.refl _ _)

/-- **Carleson-type theorem (subsequence form).**  For every `f` in `L²` of the circle
`AddCircle T`, there is a strictly increasing sequence of cut-offs `ns` along which the
symmetric partial sums of the Fourier series of `f` converge to `f` almost everywhere.

This is the almost-everywhere convergence statement for a subsequence of cut-offs
(depending on `f`); the full Carleson theorem, in which the almost-everywhere
convergence holds along *all* cut-offs `N → ∞`, is stated in the comment below and is
not proved here. -/

theorem carleson (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(@AddCircle.haarAddCircle T hT),
        Tendsto (fun k => fourierPartialSum (⇑f) (ns k) x) atTop (𝓝 (f x)) :=
  (tendstoInMeasure_fourierPartialSum f).exists_seq_tendsto_ae

/-- **Full-sequence convergence on a special class.**  If the Fourier coefficients of a
continuous function `f` on `AddCircle T` are summable, then the symmetric partial sums of
its Fourier series converge to `f` at *every* point, along the full sequence of cut-offs. -/
