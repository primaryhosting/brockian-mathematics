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

theorem parseval_fourier_norm (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- The Fourier transform on `L²`, packaged as a linear isometry equivalence. -/
