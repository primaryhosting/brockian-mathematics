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

def CompactResolventAtI.ofFactorizations {T : H →ₗ.[ℂ] H}
    (hres : ResolventAtI T)
    (Fadd : Factorization hres.Radd Eadd)
    (Fsub : Factorization hres.Rsub Esub) : CompactResolventAtI T where
  resolvent := hres
  compact_add := Fadd.isCompactOperator
  compact_sub := Fsub.isCompactOperator

/-- The canonical unit-shift resolvents on the self-adjoint closure of an
essentially self-adjoint harmonic-oscillator core. -/
