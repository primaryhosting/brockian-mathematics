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

def RightResolvent (T : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  ∀ x : H, ∃ h : R x ∈ T.domain, T ⟨R x, h⟩ - z • R x = x

end Brockian.Weyl.KatoRellichScaffold

namespace Brockian.Weyl.KatoResolventPackage

open Brockian.Weyl.KatoRellichScaffold

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded right resolvents for `T+i` and `T-i`, with the Hilbert-space
self-adjoint resolvent bound normalized at distance one from the real axis. -/
structure ResolventAtI (T : H →ₗ.[ℂ] H) where
  Radd : H →L[ℂ] H
  Rsub : H →L[ℂ] H
  right_add : RightResolvent T (-Complex.I) Radd
  right_sub : RightResolvent T Complex.I Rsub
  norm_add : ‖Radd‖ ≤ 1
  norm_sub : ‖Rsub‖ ≤ 1

end Brockian.Weyl.KatoResolventPackage

/-! ## Brockian/WeylWeightedRellich.lean -/

namespace Brockian.Weyl.WeightedRellich

open Brockian.Weyl.KatoResolventPackage

variable {H E Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- A resolvent factorization through a compactly embedded weighted space. -/
structure Factorization (R : H →L[ℂ] H) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] where
  embedding : E →L[ℂ] H
  lift : H →L[ℂ] E
  compact_embedding : IsCompactOperator embedding
  factorization : embedding.comp lift = R

omit [CompleteSpace H] in
/-- The compact-embedding factorization makes the resolvent compact. -/
