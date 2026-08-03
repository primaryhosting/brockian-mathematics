import Brockian.WeylOscillatorDiscrete

/-
Harmonic / Aristotle hard target.

Prove the concrete weighted-Rellich endpoint for the canonical unit-shift
resolvents of the oscillator closure. The ESA input is explicit so this target
does not duplicate oscillator ESA. Do not satisfy compactness by changing the
operator or by assuming a Factorization/IsCompactOperator premise.
-/
namespace Brockian.HardTargets.OscillatorCompactResolvent

open Brockian.Weyl.Operator
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.OscillatorDiscrete

theorem harmonicOscillatorClosureResolvents_compact_target
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Radd ∧
      IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Rsub := by
  sorry

end Brockian.HardTargets.OscillatorCompactResolvent
