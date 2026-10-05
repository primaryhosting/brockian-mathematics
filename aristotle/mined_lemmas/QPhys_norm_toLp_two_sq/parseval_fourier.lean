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

theorem parseval_fourier (f : 𝓢(ℝ, ℂ)) :
    ∫ w : ℝ, ‖(𝓕 f) w‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 :=
  parseval_fourier' f

/-- The `L²`-version of Parseval's theorem: the Fourier transform is an isometry of
`L²(ℝ, ℂ)`. -/
