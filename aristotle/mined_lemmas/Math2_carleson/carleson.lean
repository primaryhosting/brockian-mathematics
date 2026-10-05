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
