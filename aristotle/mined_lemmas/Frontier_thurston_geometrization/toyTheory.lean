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

def toyTheory : ThreeManifoldTheory where
  Mfld := ℕ
  sphere := 0
  csum := (· + ·)
  csum_assoc a b c := by omega
  csum_sphere a := by omega
  sphere_csum a := by omega
  IsPrime m := m = 1
  complexity m := m
  kneser_step m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨1, m - 1, by omega, by omega, by omega⟩)
  Geometric m g := m = 1 ∧ g = Geometry.S3
  GluedFrom m pieces := pieces = [m]
  jsj_geometrization m hm := ⟨[m], rfl, by
    intro q hq
    simp only [List.mem_singleton] at hq
    exact ⟨Geometry.S3, by simp [hq, hm]⟩⟩

example : ∃ T : ThreeManifoldTheory, Nonempty T.Mfld := ⟨toyTheory, ⟨(0 : ℕ)⟩⟩

end Frontier

