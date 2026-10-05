/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Fourier transform is an `L²` isometry (Plancherel/Parseval).

* `QPhys.fourier_isometry_L2` : the abstract statement, `‖𝓕 f‖ = ‖f‖` for `f ∈ L²(ℝ, ℂ)`.
* `QPhys.parseval_fourier` : the concrete Parseval identity for wave functions, i.e. for
  Schwartz functions `f g : 𝓢(ℝ, ℂ)`,
  `∫ x, conj (f x) * g x = ∫ ξ, conj (𝓕 f ξ) * 𝓕 g ξ`.
* `QPhys.plancherel_fourier_norm_sq` : the special case `f = g`, i.e. conservation of the total
  probability `∫ ‖f x‖² = ∫ ‖𝓕 f ξ‖²`.
-/

open SchwartzMap MeasureTheory FourierTransform

namespace QPhys

/-- **Plancherel's theorem**: the Fourier transform is an isometry of `L²(ℝ, ℂ)`. -/

theorem plancherel_fourier_norm_sq (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ^ 2 = ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have key := parseval_fourier f f
  simp only [hconj] at key
  rw [integral_complex_ofReal, integral_complex_ofReal] at key
  exact_mod_cast key

end QPhys

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

