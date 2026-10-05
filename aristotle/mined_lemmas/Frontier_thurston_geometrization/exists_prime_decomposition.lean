/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## The eight Thurston model geometries -/

/-- The eight three-dimensional Thurston model geometries:
`E3` (Euclidean), `S3` (spherical), `H3` (hyperbolic), `S2xR`, `H2xR`,
`SL2R` (the universal cover of `SL(2,ℝ)`), `Nil` and `Sol`. -/
inductive Geometry
  | E3
  | S3
  | H3
  | S2xR
  | H2xR
  | SL2R
  | Nil
  | Sol
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

theorem exists_prime_decomposition (T : ThreeManifoldTheory) (m : T.Mfld) :
    ∃ l : List T.Mfld, (∀ p ∈ l, T.IsPrime p) ∧ m = T.connectedSum l := by
  generalize hn : T.complexity m = n
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    rcases T.kneser_step m with h | h | ⟨a, b, rfl, ha, hb⟩
    · exact ⟨[], by simp, by simp [h]⟩
    · exact ⟨[m], by simpa using h, (T.connectedSum_singleton m).symm⟩
    · subst hn
      obtain ⟨la, hla, hea⟩ := ih (T.complexity a) ha a rfl
      obtain ⟨lb, hlb, heb⟩ := ih (T.complexity b) hb b rfl
      refine ⟨la ++ lb, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hla p hp
        · exact hlb p hp
      · rw [T.connectedSum_append, ← hea, ← heb]

/-- **Thurston's geometrization of closed 3-manifolds.**

Every closed orientable 3-manifold `m` is a finite connected sum of prime
manifolds, and each prime summand can be cut along a system of incompressible
tori into pieces, each of which admits a geometric structure modelled on one of
the eight Thurston geometries `E³, S³, H³, S²×ℝ, H²×ℝ, SL(2,ℝ)~, Nil, Sol`.

This is a Lean-checked reduction: the statement is derived from the two deep
inputs recorded in `ThreeManifoldTheory`, namely the local Kneser splitting
step (`kneser_step`) and geometrization for prime manifolds
(`jsj_geometrization`, i.e. Thurston's hyperbolization theorem together with
Perelman's proof of the elliptization conjecture). -/
