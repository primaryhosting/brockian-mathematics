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

theorem harmonicOscillatorClosureResolvents_compact_target
    (hESA : EssentiallySelfAdjoint harmonicOscillatorPMap) :
    IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Radd ∧
      IsCompactOperator (harmonicOscillatorClosureResolventAtI hESA).Rsub := by
  have hsym : IsSymmetric harmonicOscillatorPMap.closure :=
    isSymmetric_closure harmonicOscillatorPMap_isSymmetric harmonicOscillatorPMap_dense
  constructor
  · refine isCompactOperator_of_rightResolvent (z := -Complex.I) (by simp) (by simp)
      ?_ hsym
    exact (harmonicOscillatorClosureResolventAtI hESA).right_add
  · refine isCompactOperator_of_rightResolvent (z := Complex.I) (by simp) (by simp)
      ?_ hsym
    exact (harmonicOscillatorClosureResolventAtI hESA).right_sub

end Brockian.Weyl.OscillatorDiscrete

/-
  Compactness.lean — the concrete weighted-Rellich estimate for the harmonic
  oscillator core, and the compactness of the two unit-shift resolvents of its
  closure.

  The mathematical content:

  * `energy g = ∫ ‖g'‖² + ∫ x²‖g‖²` is the quadratic form of the oscillator on
    the Schwartz core (`inner_oscillatorCoreMap_self`).
  * The image of the closed unit ball under a unit-shift resolvent of the
    closure consists of `L²`-limits of Schwartz functions of energy at most `2`
    (`resolvent_mem_closure_goodSet`).
  * A set of Schwartz functions of bounded energy is, in `L²`, uniformly close
    to a fixed finite-dimensional subspace of step functions: the confining
    weight `x²` controls the tail and the kinetic term controls the oscillation
    inside each cell (`exists_finiteDimensional_approx`).
  * An operator whose unit ball image is uniformly approximable by
    finite-dimensional subspaces is compact (`isCompactOperator_of_approx`).
-/
import RequestProject.ClosureResolvent
import RequestProject.CompactCriterion
import RequestProject.Rellich

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.OscillatorCompact

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges
open Filter Topology

/-! ### The quadratic form of the oscillator -/

/-- The quadratic form of the harmonic oscillator on the Schwartz core is the
energy. -/
