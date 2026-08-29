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

  theorem carleson_full {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 (@haarAddCircle T hT)) :
      ∀ᵐ x ∂(@haarAddCircle T hT),
        Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x))

This statement is NOT established in this file: neither it nor the machinery of its proof
(the Carleson operator and its weak-type bound) is available in Mathlib.
-/

end Math2

