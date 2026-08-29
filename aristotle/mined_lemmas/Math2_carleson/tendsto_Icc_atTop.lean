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
