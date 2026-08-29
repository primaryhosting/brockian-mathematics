import Mathlib

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
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

set_option grind.warning false

/-!
## Overview

Milnor's theorem asserts that there are smooth manifolds homeomorphic, but not diffeomorphic,
to the standard 7-sphere.  His proof has two halves:

* a *geometric* half: the total spaces `M k` of certain `S³`-bundles over `S⁴` (indexed by an odd
  integer `k`) are smooth closed 7-manifolds admitting a Morse function with exactly two critical
  points, hence (Reeb) each `M k` is homeomorphic to `S⁷`; the standard sphere occurs as `M 1`;
* a *numerical* half: the Eells–Kuiper/Milnor invariant `λ`, a diffeomorphism invariant with values
  in `ZMod 7`, satisfies `λ (M k) = k ^ 2 - 1`.

Combining the two, `M 3` is homeomorphic to `S⁷` but has `λ (M 3) = 1 ≠ 0 = λ (M 1) = λ S⁷`,
so it is not diffeomorphic to `S⁷`.

This file formalises the *logical reduction*: the geometric and numerical inputs are taken as
explicit hypotheses (they are exactly Milnor's two theorems, which are far beyond the current
formalised literature), while the deduction of the existence of an exotic sphere from them —
including the `ZMod 7` arithmetic base case `3 ^ 2 - 1 ≠ 0` — is fully machine-checked.

Concretely we prove:

* `Frontier.milnor_lambda_base_case` : the arithmetic base case, `1 ^ 2 - 1 = 0` and
  `3 ^ 2 - 1 ≠ 0` in `ZMod 7`;
* `Frontier.exists_homeo_not_diffeo_of_invariant` : the abstract reduction, for arbitrary
  relations `Homeo`, `Diffeo` and an arbitrary `ZMod 7`-valued diffeomorphism invariant;
* `Frontier.reduction_hypotheses_satisfiable` : the abstract hypotheses are consistent (so the
  reduction is not vacuous);
* `Frontier.milnor_exotic_7sphere` : the reduction at the level of genuine smooth 7-manifolds
  (`Frontier.Smooth7Manifold`), with `Frontier.standardSphere7` the unit sphere in `ℝ⁸` carrying
  its usual smooth structure: given Milnor's two inputs, there is a smooth 7-manifold homeomorphic
  but not diffeomorphic to `S⁷`.
-/

namespace Frontier

/-! ## The arithmetic base case -/

/-- The base case of Milnor's argument: the invariant `λ (M k) = k ^ 2 - 1 ∈ ZMod 7` vanishes for
`k = 1` (the standard sphere) but not for `k = 3`. -/

theorem reduction_hypotheses_satisfiable :
    ∃ (α : Type) (Homeo Diffeo : α → α → Prop) (lam : α → ZMod 7) (fam : ℤ → α) (std : α),
      (∀ x y : α, Diffeo x y → Homeo x y) ∧
      fam 1 = std ∧
      (∀ k : ℤ, Odd k → Homeo (fam k) std) ∧
      (∀ x y : α, Diffeo x y → lam x = lam y) ∧
      (∀ k : ℤ, Odd k → lam (fam k) = ((k : ZMod 7)) ^ 2 - 1) := by
  refine ⟨ℤ, fun _ _ => True, fun a b => ((a : ZMod 7) ^ 2 = (b : ZMod 7) ^ 2),
    fun a => ((a : ZMod 7)) ^ 2 - 1, id, 1, ?_, rfl, ?_, ?_, ?_⟩
  · intro _ _ _; trivial
  · intro _ _; trivial
  · intro x y h; simp [h]
  · intro k _; rfl

/-! ## Smooth 7-manifolds -/

/-- The model space `ℝ⁷` with corners, used as the model for all manifolds below. -/
noncomputable abbrev I7 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 7)) (EuclideanSpace ℝ (Fin 7)) :=
  modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 7))

/-- A smooth (`C^∞`) 7-manifold: a type carrying a topology, an atlas modelled on `ℝ⁷`, and a
smooth structure. -/
structure Smooth7Manifold where
  /-- The underlying set of points of the manifold. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 7)) carrier]
  [smoothStructure : IsManifold I7 ∞ carrier]

attribute [instance] Smooth7Manifold.topology Smooth7Manifold.charts
  Smooth7Manifold.smoothStructure

/-- Two smooth 7-manifolds are homeomorphic. -/
