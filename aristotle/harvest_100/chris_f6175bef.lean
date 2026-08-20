/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The symmetric partial sum of the Fourier series of `f` at `x`:
`∑_{n = -N}^{N} (fourierCoeff f n) e^{2πinx/T}`. -/
noncomputable def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- The symmetric partial sum of the Fourier series of an `L²` function, viewed as an element
of `L²`. -/
noncomputable def fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) (N : ℕ) :
    Lp ℂ 2 (@haarAddCircle T hT) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (f : AddCircle T → ℂ) n • fourierLp 2 n

/-- The symmetric intervals `[-N, N]` are cofinal in the finite subsets of `ℤ`. -/
lemma tendsto_finset_Icc_atTop :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro M N hMN i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast hMN)) hi.1,
      le_trans hi.2 (by exact_mod_cast hMN)⟩
  · intro i
    refine ⟨i.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

/-- **Key intermediate step**: the symmetric partial sums of the Fourier series of an `L²`
function converge to it in the `L²` norm. -/
lemma tendsto_fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    Tendsto (fourierPartialSumLp f) atTop (𝓝 f) :=
  (hasSum_fourier_series_L2 f).comp tendsto_finset_Icc_atTop

/-- The coercion to functions of a finite sum in `L²` is almost everywhere the pointwise sum. -/
lemma coeFn_finset_sum_Lp {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {ι : Type*}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    ((∑ i ∈ s, F i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, (F i : α → ℂ) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hx2
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hx, Pi.add_apply, hx2]

/-- The `L²`-partial sum agrees almost everywhere with the pointwise partial sum. -/
lemma fourierPartialSumLp_coeFn (f : Lp ℂ 2 (@haarAddCircle T hT)) (N : ℕ) :
    (fourierPartialSumLp f N : AddCircle T → ℂ)
      =ᵐ[(@haarAddCircle T hT)] fourierPartialSum (f : AddCircle T → ℂ) N := by
  have h1 := coeFn_finset_sum_Lp (μ := (@haarAddCircle T hT))
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourierLp 2 n)
  have h2 : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ n : ℤ,
      ((fourierCoeff (f : AddCircle T → ℂ) n • fourierLp (T := T) 2 n : Lp ℂ 2 _) :
          AddCircle T → ℂ) x
        = fourierCoeff (f : AddCircle T → ℂ) n • fourier n x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (fourierCoeff (f : AddCircle T → ℂ) n)
      (fourierLp (T := T) 2 n), coeFn_fourierLp (T := T) 2 n] with x hx hx'
    rw [hx, Pi.smul_apply, hx']
  filter_upwards [h1, h2] with x hx hx2
  simp only [fourierPartialSum, fourierPartialSumLp]
  rw [hx]
  exact Finset.sum_congr rfl fun n _ => hx2 n

/-- Auxiliary version of convergence in measure, phrased with the `L²` partial sums. -/
lemma tendstoInMeasure_fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    TendstoInMeasure (@haarAddCircle T hT)
      (fun N : ℕ => (fourierPartialSumLp f N : AddCircle T → ℂ)) atTop
      (f : AddCircle T → ℂ) :=
  tendstoInMeasure_of_tendsto_Lp (tendsto_fourierPartialSumLp f)

/-- **Convergence in measure of Fourier series of `L²` functions** (whole sequence):
the symmetric partial Fourier sums of an `L²` function on the circle converge to it in
measure. -/
theorem tendstoInMeasure_fourierPartialSum (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    TendstoInMeasure (@haarAddCircle T hT)
      (fun N : ℕ => fourierPartialSum (f : AddCircle T → ℂ) N) atTop
      (f : AddCircle T → ℂ) :=
  (tendstoInMeasure_fourierPartialSumLp f).congr_left (fun N => fourierPartialSumLp_coeFn f N)

/-- **Carleson-type almost-everywhere convergence of Fourier series** (subsequence form).

For every `f` in `L²` of the circle `AddCircle T` there is a subsequence of the symmetric
partial Fourier sums `S_N f (x) = ∑_{n=-N}^{N} (fourierCoeff f n) e^{2πinx/T}` which converges
to `f (x)` for almost every `x`.

This is the almost-everywhere convergence statement obtained from `L²` convergence of the
Fourier series; Carleson's full theorem asserts the same convergence for the whole sequence
(i.e. with `ns = id`), which is not proved here. -/
theorem carleson (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun k => fourierPartialSum (f : AddCircle T → ℂ) (ns k) x) atTop
          (𝓝 ((f : AddCircle T → ℂ) x)) :=
  (tendstoInMeasure_fourierPartialSum f).exists_seq_tendsto_ae

/-- If the Fourier coefficients of an `L²` function are absolutely summable, then the symmetric
partial sums of its Fourier series converge to it almost everywhere (full sequence, no
subsequence extraction). -/
theorem carleson_of_summable_fourierCoeff (f : Lp ℂ 2 (@haarAddCircle T hT))
    (h : Summable (fourierCoeff (f : AddCircle T → ℂ))) :
    ∀ᵐ x ∂(@haarAddCircle T hT),
      Tendsto (fun N => fourierPartialSum (f : AddCircle T → ℂ) N x) atTop
        (𝓝 ((f : AddCircle T → ℂ) x)) := by
  -- The Fourier series sums to a continuous function `g`.
  have hsum : Summable (fun n : ℤ =>
      fourierCoeff (f : AddCircle T → ℂ) n • (fourier n : C(AddCircle T, ℂ))) := by
    apply Summable.of_norm
    simpa only [norm_smul, fourier_norm, mul_one] using h.norm
  obtain ⟨g, hg⟩ := hsum
  -- `g` has the same Fourier coefficients as `f`, hence `f = g` in `L²`.
  have hgLp : HasSum (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourierLp (T := T) 2 n)
      (ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ g) := by
    have := ((ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ).hasSum hg)
    refine this.congr_fun fun n => ?_
    simp [fourierLp]
  have hfg : ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ g = f :=
    hgLp.unique (hasSum_fourier_series_L2 f)
  have hae : (f : AddCircle T → ℂ) =ᵐ[(@haarAddCircle T hT)] (g : AddCircle T → ℂ) := by
    have := ContinuousMap.coeFn_toLp (p := 2) (μ := (@haarAddCircle T hT)) (𝕜 := ℂ) g
    rw [hfg] at this
    exact this
  -- Pointwise, the partial sums converge to `g`.
  have hpt : ∀ x : AddCircle T, Tendsto
      (fun N => fourierPartialSum (f : AddCircle T → ℂ) N x) atTop (𝓝 (g x)) := by
    intro x
    have hx : HasSum (fun n : ℤ => fourierCoeff (f : AddCircle T → ℂ) n • fourier n x) (g x) := by
      simpa using (ContinuousMap.evalCLM ℂ x).hasSum hg
    exact hx.comp tendsto_finset_Icc_atTop
  filter_upwards [hae] with x hx
  rw [hx]
  exact hpt x

/-
Scope note.  Carleson's theorem in its full strength is the statement

  theorem carleson_full (f : Lp ℂ 2 (@haarAddCircle T hT)) :
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun N => fourierPartialSum (f : AddCircle T → ℂ) N x) atTop
          (𝓝 ((f : AddCircle T → ℂ) x))

i.e. the whole sequence of partial sums converges almost everywhere.  This is *not* proved in
this file; what is established here is

* `Math2.tendstoInMeasure_fourierPartialSum`: the whole sequence of partial sums converges to
  `f` in measure (for every `f ∈ L²`);
* `Math2.carleson`: consequently some subsequence converges to `f` almost everywhere (for
  every `f ∈ L²`);
* `Math2.carleson_of_summable_fourierCoeff`: the whole sequence converges almost everywhere
  whenever the Fourier coefficients of `f` are absolutely summable.
-/

end Math2

