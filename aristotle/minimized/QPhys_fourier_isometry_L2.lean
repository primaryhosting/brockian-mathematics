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

theorem fourier_isometry_L2 (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- **Parseval's identity** for Schwartz-class wave functions on the line: the Fourier transform
preserves the `L²` inner product,
`∫ x, conj (f x) * g x = ∫ ξ, conj (𝓕 f ξ) * (𝓕 g) ξ`. -/
