import Brockian.WeylMaximalMultiplication
import Brockian.WeylHarmonicOscillator

/-
Harmonic / Aristotle hard target.

Statement fidelity is mandatory: prove ESA for the concrete Schwartz-core
operator already defined in Brockian. Do not replace it by the maximal x^2
multiplier, the Fourier-defined free Laplacian, or an abstract operator carrying
ESA as a hypothesis.
-/
namespace Brockian.HardTargets.OscillatorESA

open Brockian.Weyl.Operator
open Brockian.Weyl.HarmonicOscillator

theorem harmonicOscillatorPMap_essentiallySelfAdjoint_target :
    EssentiallySelfAdjoint harmonicOscillatorPMap := by
  sorry

end Brockian.HardTargets.OscillatorESA
