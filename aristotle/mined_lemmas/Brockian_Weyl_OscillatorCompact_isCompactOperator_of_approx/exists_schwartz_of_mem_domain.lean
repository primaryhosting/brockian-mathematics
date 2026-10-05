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

theorem exists_schwartz_of_mem_domain (v : harmonicOscillatorPMap.domain) :
    ∃ g : SchwartzMap ℝ ℂ, (v : L2R) = schwartzToL2 g ∧
      harmonicOscillatorPMap v = oscillatorCoreMap g := by
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp v.2
  refine ⟨g, hg.symm, ?_⟩
  have hve : v = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hve, harmonicOscillatorPMap_toFun_ofInjective]

/-- Elements of the domain of the closure are graph limits of Schwartz
functions. -/
