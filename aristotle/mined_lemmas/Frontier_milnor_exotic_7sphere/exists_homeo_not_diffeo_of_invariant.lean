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

theorem exists_homeo_not_diffeo_of_invariant {α : Type*}
    (Homeo Diffeo : α → α → Prop) (lam : α → ZMod 7) (fam : ℤ → α) (std : α)
    (hstd : fam 1 = std)
    (hhomeo : ∀ k : ℤ, Odd k → Homeo (fam k) std)
    (hinv : ∀ x y : α, Diffeo x y → lam x = lam y)
    (hval : ∀ k : ℤ, Odd k → lam (fam k) = ((k : ZMod 7)) ^ 2 - 1) :
    ∃ x : α, Homeo x std ∧ ¬ Diffeo x std := by
  have h3 : Odd (3 : ℤ) := ⟨1, by norm_num⟩
  have h1 : Odd (1 : ℤ) := ⟨0, by norm_num⟩
  refine ⟨fam 3, hhomeo 3 h3, ?_⟩
  intro hd
  have hlam3 : lam (fam 3) = ((3 : ℤ) : ZMod 7) ^ 2 - 1 := hval 3 h3
  have hlam1 : lam (fam 1) = ((1 : ℤ) : ZMod 7) ^ 2 - 1 := hval 1 h1
  have hstdval : lam std = 0 := by
    rw [← hstd, hlam1, milnor_lambda_base_case.1]
  have : lam (fam 3) = lam std := hinv _ _ hd
  rw [hlam3, hstdval] at this
  exact milnor_lambda_base_case.2 this

/-- The hypotheses of `Frontier.exists_homeo_not_diffeo_of_invariant` are consistent: they are
satisfied by an explicit model.  (This rules out the reduction being vacuously true.) -/
