/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring `/-! ... -/` before `import`; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
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

namespace QPhys

open MeasureTheory SchwartzMap FourierTransform

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The squared `L²`-norm of (the `L²`-class of) a Schwartz function is the integral of the
squared pointwise norm. -/

theorem parseval_fourier' (f : 𝓢(V, ℂ)) :
    ∫ w : V, ‖(𝓕 f) w‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  rw [← norm_toLp_two_sq, ← norm_toLp_two_sq, norm_fourier_toL2_eq f]

end

/-- **Parseval's theorem for the Fourier transform** (Plancherel), on the real line:
for every Schwartz function `f : ℝ → ℂ`, the Fourier transform preserves the `L²`-energy,
`∫ |𝓕f(w)|² dw = ∫ |f(x)|² dx`. -/
