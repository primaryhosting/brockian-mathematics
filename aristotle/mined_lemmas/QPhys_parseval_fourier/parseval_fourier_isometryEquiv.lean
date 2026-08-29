import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory FourierTransform ComplexInnerProductSpace

namespace QPhys

section General

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Parseval/Plancherel theorem.** The Fourier transform on `L²` preserves inner products:
`⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` for all `f g : L²(E, F)`.  In particular (see
`QPhys.parseval_fourier_norm`) it is an isometry of `L²`. -/

theorem parseval_fourier_isometryEquiv :
    ∃ U : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2), ∀ f : Lp (α := E) F 2, U f = 𝓕 f :=
  ⟨MeasureTheory.Lp.fourierTransformₗᵢ E F, fun _ => rfl⟩

end General

/-- Parseval's identity for complex-valued `L²` functions on the line:
`∫ ‖𝓕 f‖² = ∫ ‖f‖²`. -/
