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

theorem harmonicOscillatorPMap_isSymmetric :
    IsSymmetric harmonicOscillatorPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, harmonicOscillatorPMap_toFun_ofInjective,
    harmonicOscillatorPMap_toFun_ofInjective, LinearEquiv.ofInjective_apply,
    LinearEquiv.ofInjective_apply]
  exact oscillatorCoreMap_symm f g

end Brockian.Weyl.HarmonicOscillator

/-
  OscillatorDiscrete.lean — `Brockian/WeylOscillatorDiscrete.lean` together with
  the target theorem: the two canonical unit-shift resolvents of the harmonic
  oscillator closure are compact operators.
-/
import RequestProject.Compactness

namespace Brockian.Weyl.OscillatorDiscrete

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.ClosedShiftedRanges
open Brockian.Weyl.WeightedRellich
open Brockian.Weyl.HarmonicOscillator
open Brockian.Weyl.OscillatorCompact

variable {H Eadd Esub : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Eadd] [NormedSpace ℂ Eadd]
  [NormedAddCommGroup Esub] [NormedSpace ℂ Esub]

/-- Both canonical unit-shift resolvents of an operator, together with proofs
that they are compact operators. -/
structure CompactResolventAtI (T : H →ₗ.[ℂ] H) where
  resolvent : ResolventAtI T
  compact_add : IsCompactOperator resolvent.Radd
  compact_sub : IsCompactOperator resolvent.Rsub

/-- Weighted-Rellich factorizations construct a compact-resolvent package. -/
