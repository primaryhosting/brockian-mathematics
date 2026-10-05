import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

noncomputable section

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- For an `L²` function, the integral of the squared norm is the square of the `L²` norm. -/

theorem inner_fourier_eq_inner (f g : Lp (α := V) H 2) :
    ∫ ξ : V, (inner ℂ (((𝓕 f : Lp (α := V) H 2)) ξ) (((𝓕 g : Lp (α := V) H 2)) ξ) : ℂ)
      = ∫ x : V, (inner ℂ ((f : V → H) x) ((g : V → H) x) : ℂ) := by
  rw [← L2.inner_def, ← L2.inner_def, Lp.inner_fourier_eq]

/-- **Parseval's theorem in explicit integral form**, for Schwartz functions on the line:
the Fourier integral `𝓕 f ξ = ∫ x, exp (-2πi x ξ) f x` preserves the `L²` norm. -/
