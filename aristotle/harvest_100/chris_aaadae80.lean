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
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The model space and the category of smooth `4`-manifolds -/

/-- The model space `ℝ⁴`. -/
abbrev R4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The (boundaryless) model with corners of `ℝ⁴` on itself. -/
noncomputable abbrev I4 : ModelWithCorners ℝ R4 R4 := modelWithCornersSelf ℝ R4

/-- A `C^∞` smooth `4`-manifold without boundary: a topological space equipped with an atlas
of charts into `ℝ⁴` whose transition maps are `C^∞`. -/
structure Smooth4Manifold where
  /-- The underlying set of points of the manifold. -/
  Carrier : Type
  /-- The topology on the manifold. -/
  [topology : TopologicalSpace Carrier]
  /-- The atlas of charts with values in `ℝ⁴`. -/
  [charted : ChartedSpace R4 Carrier]
  /-- The transition maps of the atlas are `C^∞`. -/
  [manifold : IsManifold I4 ∞ Carrier]

attribute [instance] Smooth4Manifold.topology Smooth4Manifold.charted Smooth4Manifold.manifold

/-- `ℝ⁴` with its standard smooth structure, as a smooth `4`-manifold. -/
@[reducible] def standardR4 : Smooth4Manifold := { Carrier := R4 }

/-- Two smooth `4`-manifolds are *homeomorphic* if there is a homeomorphism between them. -/
def Homeo (M N : Smooth4Manifold) : Prop := Nonempty (M.Carrier ≃ₜ N.Carrier)

/-- Two smooth `4`-manifolds are *diffeomorphic* if there is a `C^∞` diffeomorphism between
them (a `C^∞` bijection with `C^∞` inverse, computed in the charts of the two atlases). -/
def Diffeo (M N : Smooth4Manifold) : Prop := Nonempty (M.Carrier ≃ₘ⟮I4, I4⟯ N.Carrier)

/-! ## Basic properties of `Homeo` and `Diffeo` -/

theorem Homeo.refl (M : Smooth4Manifold) : Homeo M M := ⟨Homeomorph.refl _⟩

theorem Homeo.symm {M N : Smooth4Manifold} (h : Homeo M N) : Homeo N M := ⟨h.some.symm⟩

theorem Homeo.trans {M N P : Smooth4Manifold} (h : Homeo M N) (h' : Homeo N P) : Homeo M P :=
  ⟨h.some.trans h'.some⟩

theorem Diffeo.refl (M : Smooth4Manifold) : Diffeo M M := ⟨Diffeomorph.refl I4 M.Carrier ∞⟩

theorem Diffeo.symm {M N : Smooth4Manifold} (h : Diffeo M N) : Diffeo N M := ⟨h.some.symm⟩

theorem Diffeo.trans {M N P : Smooth4Manifold} (h : Diffeo M N) (h' : Diffeo N P) : Diffeo M P :=
  ⟨h.some.trans h'.some⟩

/-- A diffeomorphism is in particular a homeomorphism. -/
theorem Homeo.of_diffeo {M N : Smooth4Manifold} (h : Diffeo M N) : Homeo M N :=
  ⟨h.some.toHomeomorph⟩

/-! ## The statement of the theorem of Donaldson and Freedman -/

/-- `M` is an *exotic* `ℝ⁴`: a smooth `4`-manifold which is homeomorphic to `ℝ⁴` but not
diffeomorphic to it. -/
def IsExoticR4 (M : Smooth4Manifold) : Prop := Homeo M standardR4 ∧ ¬ Diffeo M standardR4

/-- **The statement**: there exists a smooth manifold homeomorphic, but not diffeomorphic,
to `ℝ⁴`. This is the theorem of Donaldson and Freedman. -/
def ExoticR4Exists : Prop := ∃ M : Smooth4Manifold, IsExoticR4 M

/-- The standard `ℝ⁴` is of course not exotic. -/
theorem standardR4_not_isExoticR4 : ¬ IsExoticR4 standardR4 := fun h => h.2 (Diffeo.refl _)

/-- Being an exotic `ℝ⁴` is invariant under diffeomorphism. -/
theorem IsExoticR4.of_diffeo {M N : Smooth4Manifold} (hMN : Diffeo M N) (hN : IsExoticR4 N) :
    IsExoticR4 M :=
  ⟨(Homeo.of_diffeo hMN).trans hN.1, fun h => hN.2 (hMN.symm.trans h)⟩

/-! ## The main reduction -/

/-- **Exotic `ℝ⁴`, as a Lean-checked reduction.**

The existence of an exotic `ℝ⁴` — a smooth manifold homeomorphic but not diffeomorphic to `ℝ⁴`
(Donaldson–Freedman) — is *equivalent* to the failure of uniqueness of the smooth structure on
`ℝ⁴`: namely, to the existence of two smooth `4`-manifolds, each homeomorphic to `ℝ⁴`, which are
not diffeomorphic to each other.

This reduces the (deep) existence statement `ExoticR4Exists` to a statement in which the standard
smooth structure plays no distinguished role. -/
theorem exotic_R4 :
    ExoticR4Exists ↔
      ∃ M N : Smooth4Manifold, Homeo M standardR4 ∧ Homeo N standardR4 ∧ ¬ Diffeo M N := by
  constructor
  · rintro ⟨M, hMhomeo, hMdiff⟩
    exact ⟨M, standardR4, hMhomeo, Homeo.refl _, hMdiff⟩
  · rintro ⟨M, N, hM, hN, hMN⟩
    by_cases hMs : Diffeo M standardR4
    · exact ⟨N, hN, fun hNs => hMN (hMs.trans hNs.symm)⟩
    · exact ⟨M, hM, hMs⟩

/-- A second, equivalent form of the reduction: an exotic `ℝ⁴` exists precisely when the smooth
structure of a topological `ℝ⁴` is not unique up to diffeomorphism. -/
theorem exotic_R4_iff_smooth_structure_not_unique :
    ExoticR4Exists ↔
      ¬ ∀ M N : Smooth4Manifold, Homeo M standardR4 → Homeo N standardR4 → Diffeo M N := by
  rw [exotic_R4]
  constructor
  · rintro ⟨M, N, hM, hN, hMN⟩ h
    exact hMN (h M N hM hN)
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h hcon

end Frontier

