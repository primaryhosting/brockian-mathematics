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

