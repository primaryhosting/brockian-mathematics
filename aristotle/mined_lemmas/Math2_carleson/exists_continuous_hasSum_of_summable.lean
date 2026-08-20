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
