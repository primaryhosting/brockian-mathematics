/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

noncomputable def harmonicOscillatorClosureResolventAtI
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    ResolventAtI harmonicOscillatorPMap.closure :=
  closureResolventAtIOfEssentiallySelfAdjoint
    harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense hESA

/-- **The concrete weighted-Rellich endpoint.** Both canonical unit-shift
resolvents `(T̄ ± i)⁻¹` of the closure of the harmonic-oscillator core are
compact operators. -/
