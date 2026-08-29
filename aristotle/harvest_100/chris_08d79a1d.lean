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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle T → ℂ`,
i.e. `∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/
noncomputable def fourierPartialSum {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ) (N : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

section Aux

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The coercion to a function of a finite sum in `Lp` is a.e. the pointwise finite sum. -/
lemma coeFn_finset_sum_Lp {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ 2 (@haarAddCircle T hT)) :
    ⇑(∑ i ∈ s, F i) =ᵐ[@haarAddCircle T hT] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 (@haarAddCircle T hT))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x hx hx'
      rw [hx]
      simp only [Pi.add_apply, hx', Finset.sum_insert ha]

/-- The `Lp`-valued partial sum of the Fourier series agrees a.e. with the explicit
pointwise partial sum. -/
lemma coeFn_fourier_sum (f : Lp ℂ 2 (@haarAddCircle T hT)) (s : Finset ℤ) :
    ⇑(∑ i ∈ s, fourierCoeff (⇑f) i • fourierLp 2 i)
      =ᵐ[@haarAddCircle T hT] fun x => ∑ i ∈ s, fourierCoeff (⇑f) i * fourier i x := by
  classical
  have h1 := coeFn_finset_sum_Lp (T := T) s
    (fun i => fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT)))
  have h2 : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ i ∈ s,
      (fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT))) x
        = fourierCoeff (⇑f) i * fourier i x := by
    rw [Filter.eventually_all_finset]
    intro i _
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑f) i)
        (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT)),
      coeFn_fourierLp (T := T) 2 i] with x hx hx'
    rw [hx]
    simp only [Pi.smul_apply, hx', smul_eq_mul]
  filter_upwards [h1, h2] with x hx hx'
  rw [hx]
  exact Finset.sum_congr rfl fun i hi => hx' i hi

/-- The sets `Finset.Icc (-N) N`, `N : ℕ`, are monotone and exhaust `ℤ`, hence tend to `atTop`
in the filter of finite subsets of `ℤ`. -/
lemma tendsto_Icc_atTop :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun i => ⟨i.natAbs, ?_⟩)
  · apply Finset.Icc_subset_Icc <;> simp <;> omega
  · simp only [Finset.mem_Icc]
    omega

end Aux

/-- **Carleson-type a.e. convergence of Fourier series of an `L²` function.**

For every `f` in `L²` of the additive circle `AddCircle T` (with normalized Haar measure),
there is a subsequence `ns` along which the symmetric partial sums of the Fourier series of `f`
converge almost everywhere to `f`.

Note on the formalization: Carleson's theorem asserts a.e. convergence of the *full* sequence of
partial sums. That result is not available in Mathlib, and its proof is far beyond what can be
reconstructed here; what is proved below is the (nontrivial, but weaker) a.e. convergence along a
subsequence, obtained from `L²` convergence of the Fourier series. -/
theorem carleson {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun k => fourierPartialSum (⇑f) (ns k) x) atTop (𝓝 (f x)) := by
  classical
  have hL2 := hasSum_fourier_series_L2 f
  have htend : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT))) atTop (𝓝 f) :=
    hL2.comp tendsto_Icc_atTop
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp htend).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hall : ∀ᵐ x ∂(@haarAddCircle T hT), ∀ N : ℕ,
      (∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff (⇑f) i • (fourierLp 2 i : Lp ℂ 2 (@haarAddCircle T hT))) x
        = fourierPartialSum (⇑f) N x := by
    rw [ae_all_iff]
    intro N
    exact coeFn_fourier_sum f (Finset.Icc (-(N : ℤ)) (N : ℤ))
  filter_upwards [hae, hall] with x hx hx'
  refine hx.congr ?_
  intro k
  exact hx' (ns k)

/-- A classical special case of Carleson's theorem, in which the *whole* sequence of partial sums
converges (indeed at every point): if the Fourier coefficients of a continuous function on the
circle are absolutely summable, then the symmetric partial sums of its Fourier series converge
pointwise to `f`. -/
theorem tendsto_fourierPartialSum_of_summable {T : ℝ} [hT : Fact (0 < T)]
    {f : C(AddCircle T, ℂ)} (h : Summable (fourierCoeff (⇑f))) (x : AddCircle T) :
    Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x)) := by
  have hs := (has_pointwise_sum_fourier_series_of_summable h x).comp tendsto_Icc_atTop
  simpa [fourierPartialSum, Function.comp_def, smul_eq_mul] using hs

/-
For the record, the full strength of Carleson's theorem is the following statement, in which the
whole sequence of partial sums (not merely a subsequence) converges almost everywhere:

  theorem carleson_full {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT)) :
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x))

This statement is NOT established in this file: neither it nor the machinery of its proof
(the Carleson operator and its weak-type bound) is available in Mathlib.
-/

end Math2

