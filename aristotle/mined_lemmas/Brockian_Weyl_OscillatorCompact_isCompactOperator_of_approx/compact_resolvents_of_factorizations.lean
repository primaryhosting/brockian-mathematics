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

theorem compact_resolvents_of_factorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) :
    IsCompactOperator hres.Radd ∧ IsCompactOperator hres.Rsub :=
  ⟨Fadd.isCompactOperator, Fsub.isCompactOperator⟩

end Brockian.Weyl.WeightedRellich

/-! ## Brockian/WeylClosedShiftedRanges.lean (reconstruction) -/

namespace Brockian.Weyl.ClosedShiftedRanges

open Brockian.Weyl.Operator
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoResolventPackage
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range of the shifted operator `T - z`. -/
