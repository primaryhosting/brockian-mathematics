/-
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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
