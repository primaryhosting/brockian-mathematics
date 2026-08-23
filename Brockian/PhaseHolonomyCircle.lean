import Brockian.Characters5
import Brockian.PhaseDepthClassification

/-!
# Fifth-root-valued realization of finite phase-depth holonomy

The correct first geometric target for a `ZMod 5` phase-depth cocycle is torsion-sensitive
unit-circle holonomy, not ordinary real de Rham cohomology.  Mathlib supplies the canonical
injective additive character

`ZMod 5 → rootsOfUnity 5 Circle`.

Composing it with `PhaseDepthClassification.totalDepth` realizes the complete discrete gauge
invariant as a fifth root of unity.  This module packages the holonomy representation itself;
constructing a line bundle with flat connection and proving that its analytic holonomy agrees
with this value remain separate obligations.
-/

namespace Brockian.PhaseHolonomyCircle

open Brockian.PhaseDepthClassification

/-- The canonical faithful character from additive phase depth to fifth roots in `U(1)`. -/
noncomputable def phaseCharacter : AddChar (ZMod 5) (rootsOfUnity 5 Circle) :=
  ZMod.rootsOfUnityAddChar 5

/-- Fifth-root-valued holonomy of a phase-depth edge cocycle. -/
noncomputable def phaseHolonomy (c : ZMod 5 → ZMod 5) : rootsOfUnity 5 Circle :=
  phaseCharacter (totalDepth c)

/-- The fifth-root character used here is the unit-circle lift of the repository's existing
complex character `Characters5.e`. -/
theorem phaseCharacter_coe_eq_e (k : ZMod 5) :
    (((phaseCharacter k).val : Circle) : ℂ) = Brockian.Characters5.e k := by
  rw [Brockian.Characters5.e_eq_stdAddChar, ZMod.stdAddChar_apply]
  rfl

/-- Gauge-equivalent edge cocycles have identical fifth-root holonomy. -/
theorem phaseHolonomy_eq_of_cohomologous {c₁ c₂ : ZMod 5 → ZMod 5}
    (h : Cohomologous c₁ c₂) : phaseHolonomy c₁ = phaseHolonomy c₂ := by
  unfold phaseHolonomy
  rw [totalDepth_eq_of_cohomologous h]

/-- Fifth-root holonomy is a complete invariant of the single-cycle gauge class. -/
theorem cohomologous_iff_phaseHolonomy_eq {c₁ c₂ : ZMod 5 → ZMod 5} :
    Cohomologous c₁ c₂ ↔ phaseHolonomy c₁ = phaseHolonomy c₂ := by
  rw [cohomologous_iff_totalDepth_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    apply ZMod.injective_toCircle (N := 5)
    exact congrArg (fun z : rootsOfUnity 5 Circle ↦ z.val) h

end Brockian.PhaseHolonomyCircle
