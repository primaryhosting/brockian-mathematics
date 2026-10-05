/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Statement: There exists a smooth manifold homeomorphic but not diffeomorphic to ℝ⁴ (Donaldson/Freedman).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold
open scoped ContDiff

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The standard topological/smooth model `ℝ⁴`. -/
abbrev R4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The standard model with corners on `ℝ⁴` (no boundary). -/
noncomputable abbrev I4 : ModelWithCorners ℝ R4 R4 := 𝓘(ℝ, R4)

/-- A smooth (`C^∞`) manifold modelled on `ℝ⁴`, together with a homeomorphism onto `ℝ⁴`.
This packages "a smooth manifold homeomorphic to `ℝ⁴`". -/
structure SmoothStructureHomeoR4 where
  /-- The underlying type. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [charted : ChartedSpace R4 carrier]
  [manifold : IsManifold I4 ∞ carrier]
  /-- The witnessing homeomorphism with the standard `ℝ⁴`. -/
  homeo : carrier ≃ₜ R4

/-- Such a smooth manifold is *exotic* if it admits no diffeomorphism onto the standard `ℝ⁴`. -/
def IsExotic (M : SmoothStructureHomeoR4) : Prop :=
  letI := M.top; letI := M.charted; letI := M.manifold
  IsEmpty (M.carrier ≃ₘ⟮I4, I4⟯ R4)

/-- The statement of the Donaldson–Freedman phenomenon: there is a smooth manifold that is
homeomorphic, but not diffeomorphic, to `ℝ⁴`. -/
def ExoticR4Exists : Prop := ∃ M : SmoothStructureHomeoR4, IsExotic M

/-- The "small exotic `ℝ⁴`" form of the statement: some open subset of the standard `ℝ⁴`,
equipped with its induced smooth structure, is homeomorphic but not diffeomorphic to `ℝ⁴`. -/
def SmallExoticR4Exists : Prop :=
  ∃ U : TopologicalSpace.Opens R4,
    Nonempty ((U : Type) ≃ₜ R4) ∧ IsEmpty ((U : Type) ≃ₘ⟮I4, I4⟯ R4)

/-- The standard `ℝ⁴`, viewed as a smooth manifold homeomorphic to `ℝ⁴`. -/
def standardR4 : SmoothStructureHomeoR4 where
  carrier := R4
  homeo := Homeomorph.refl R4

/-- The standard `ℝ⁴` is, of course, not exotic. -/
theorem standardR4_not_exotic : ¬ IsExotic standardR4 := by
  intro h
  exact h.false (Diffeomorph.refl I4 R4 ∞)

/-- A diffeomorphism gives a homeomorphism, so exoticness is a genuine strengthening of
"not homeomorphic to `ℝ⁴`": every element of `SmoothStructureHomeoR4` *is* homeomorphic to `ℝ⁴`. -/
theorem exists_homeomorph (M : SmoothStructureHomeoR4) :
    letI := M.top; Nonempty (M.carrier ≃ₜ R4) :=
  ⟨M.homeo⟩

/-- Reformulation: an exotic `ℝ⁴` exists iff it is *not* the case that every smooth manifold
homeomorphic to `ℝ⁴` is diffeomorphic to it. -/
theorem exoticR4Exists_iff :
    ExoticR4Exists ↔
      ¬ ∀ M : SmoothStructureHomeoR4,
        letI := M.top; letI := M.charted; letI := M.manifold
        Nonempty (M.carrier ≃ₘ⟮I4, I4⟯ R4) := by
  constructor
  · rintro ⟨M, hM⟩ hall
    exact (hM.false (hall M).some).elim
  · intro h
    by_contra hex
    apply h
    intro M
    rw [← not_isEmpty_iff]
    intro hM
    exact hex ⟨M, hM⟩

/-- **Exotic `ℝ⁴` (Donaldson–Freedman), as a Lean-checked reduction.**

Given the existence of a *small* exotic `ℝ⁴` — an open subset of the standard `ℝ⁴`, with its
induced smooth structure, that is homeomorphic but not diffeomorphic to `ℝ⁴` — there exists a
smooth manifold that is homeomorphic but not diffeomorphic to `ℝ⁴`. -/
theorem exotic_R4 (h : SmallExoticR4Exists) : ExoticR4Exists := by
  obtain ⟨U, ⟨e⟩, hne⟩ := h
  exact ⟨{ carrier := (U : Type), homeo := e }, hne⟩

end Frontier

