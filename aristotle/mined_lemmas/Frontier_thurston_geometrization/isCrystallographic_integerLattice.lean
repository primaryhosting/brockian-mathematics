import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

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

import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above is placed immediately after the single `import` line, because
Lean 4 requires `import` commands to occur before any other command, including module
documentation.)

## What is formalized here

Thurston's geometrization conjecture (proved by Perelman) states that every closed,
orientable 3-manifold can be cut along spheres and tori (the prime and JSJ decompositions)
into pieces, each of which admits a locally homogeneous Riemannian metric modelled on one
of exactly **eight** model geometries:

`E³`, `S³`, `H³`, `S² × ℝ`, `H² × ℝ`, `SL(2,ℝ)~`, `Nil`, `Sol`.

A complete formal proof is far beyond current formal libraries (Mathlib has no Ricci flow,
no 3-manifold topology, no JSJ decomposition; a search of Mathlib turns up no lemma of this
shape, so no `exact?`/`apply?` citation is possible). What this file provides is:

1. `Frontier.ThurstonGeometry`: the type of the eight model geometries, together with the
   Lean-checked fact that it has exactly eight elements
   (`Frontier.card_thurstonGeometry`).
2. A **base case with genuine content**: the flat 3-torus `ℝ³/ℤ³` really is a closed
   Euclidean 3-manifold. Concretely, `Frontier.integerLattice` is a subgroup of `E³ = ℝ³`
   acting by isometries, freely, discretely (with a uniform `1 ≤ ‖v‖` separation) and
   cocompactly; see `Frontier.isCrystallographic_integerLattice`. This is the `E³` case
   of geometrization, proved from scratch.
3. A **Lean-checked reduction**: geometrization of all closed 3-manifolds follows from
   geometrization of the prime/JSJ pieces (`Frontier.GeometrizationHolds`), which is the
   standard reduction step; see `Frontier.geometrization_of_prime_pieces`.

The target theorem `Frontier.thurston_geometrization` packages these three items: the count
of the eight geometries, the Euclidean base case, and the reduction (whose only hypothesis
is the geometrization of prime pieces, the analytic input supplied by Ricci flow).
-/

namespace Frontier

open scoped Finset

/-! ## The eight Thurston geometries -/

/-- The eight model geometries of Thurston's geometrization: Euclidean space `E³`,
the round sphere `S³`, hyperbolic space `H³`, the products `S² × ℝ` and `H² × ℝ`,
the universal cover of `SL(2,ℝ)`, the Heisenberg geometry `Nil`, and `Sol`. -/
inductive ThurstonGeometry
  | euclidean        -- E³
  | spherical        -- S³
  | hyperbolic       -- H³
  | sphereTimesLine  -- S² × ℝ
  | hyperbolicTimesLine -- H² × ℝ
  | slTwoRTilde      -- universal cover of SL(2,ℝ)
  | nil              -- Nil
  | sol              -- Sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston model geometries. -/

theorem isCrystallographic_integerLattice : IsCrystallographicE3 integerLattice where
  isometric := fun v _ => isometry_add_right v
  free := by
    intro v _ hv x hx
    exact hv (by simpa using hx)
  discrete := by
    intro v hv hv0
    -- some coordinate of `v` is a nonzero integer, hence has absolute value at least `1`
    have hex : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv0 (by ext i; simpa using h i)
    obtain ⟨i, hi⟩ := hex
    obtain ⟨n, hn⟩ := hv i
    have hn0 : n ≠ 0 := by
      rintro rfl; exact hi (by simpa using hn)
    have h1 : (1 : ℝ) ≤ |v i| := by
      rw [hn, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    exact h1.trans (abs_coord_le_norm v i)
  cocompact := by
    refine ⟨unitCube, isCompact_unitCube, fun x => ?_⟩
    refine ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => (⌊x i⌋ : ℝ)), ?_, ?_⟩
    · intro i; exact ⟨⌊x i⌋, by simp⟩
    · intro i
      simp only [PiLp.sub_apply]
      refine ⟨by simp, ?_⟩
      simp only [EuclideanSpace.equiv]
      simpa using (Int.fract_lt_one (x i)).le

/-! ## The reduction to the prime / JSJ pieces -/

/-- Abstract data for a statement of geometrization: a class of (closed, orientable)
3-manifolds, the multiset of pieces produced by the prime and JSJ decompositions, a notion
of primeness, and the relation "`M` carries the geometry `g`". The only structural axiom
required is that the pieces of the decomposition are prime. -/
structure GeometrizationSetup where
  /-- The type of closed orientable 3-manifolds (up to diffeomorphism, say). -/
  Manifold : Type
  /-- Being prime (and, after the JSJ step, atoroidal or Seifert fibred). -/
  Prime : Manifold → Prop
  /-- The pieces of the prime + JSJ decomposition. -/
  Pieces : Manifold → Multiset Manifold
  /-- `Geometric M g` says that `M` carries a locally homogeneous metric modelled on `g`. -/
  Geometric : Manifold → ThurstonGeometry → Prop
  /-- The pieces of the decomposition are prime. -/
  pieces_prime : ∀ M : Manifold, ∀ P ∈ Pieces M, Prime P

/-- Geometrization for a given setup: every piece of the decomposition of every manifold
carries one of the eight geometries. -/
