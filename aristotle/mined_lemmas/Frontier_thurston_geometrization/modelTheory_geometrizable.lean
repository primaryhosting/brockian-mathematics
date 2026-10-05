-- (Lean 4 requires `import` to be the very first command in a file, so the
-- module docstring header below follows the import.)
import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## 1. The eight Thurston geometries

Thurston's list of the eight maximal, simply connected, three–dimensional model
geometries admitting a compact quotient:

`E³`, `S³`, `H³`, `S² × ℝ`, `H² × ℝ`, `SL(2,ℝ)~`, `Nil`, `Sol`.
-/

/-- The eight three–dimensional Thurston model geometries. -/
inductive Geometry where
  /-- Euclidean geometry `E³`. -/
  | euclidean : Geometry
  /-- Spherical geometry `S³`. -/
  | spherical : Geometry
  /-- Hyperbolic geometry `H³`. -/
  | hyperbolic : Geometry
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine : Geometry
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicTimesLine : Geometry
  /-- The geometry of the universal cover of `SL(2,ℝ)`. -/
  | slTwoRCover : Geometry
  /-- Nil geometry (the Heisenberg group). -/
  | nil : Geometry
  /-- Sol geometry (the three-dimensional solvable Lie group). -/
  | sol : Geometry
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/

theorem modelTheory_geometrizable :
    ∀ m : modelTheory.Mfld, ∃ ps : List modelTheory.Piece, modelTheory.IsJSJ m ps ∧
      ∀ p ∈ ps, ∃ g : Geometry, modelTheory.AdmitsGeometry p g := by
  refine thurston_geometrization modelTheory (fun n => (n : ℕ))
    (fun a => Nat.add_zero a) (fun a => Nat.zero_add a) (fun a b c => Nat.add_assoc a b c)
    ?_ ?_ ⟨[], rfl, by simp⟩ ?_
  · show ∀ m : ℕ, m = 1 ∨ m = 0 ∨ ∃ a b : ℕ, m = a + b ∧ a < m ∧ b < m
    intro m
    match m with
    | 0 => exact Or.inr (Or.inl rfl)
    | 1 => exact Or.inl rfl
    | (n + 2) => exact Or.inr (Or.inr ⟨1, n + 1, by omega, by omega, by omega⟩)
  · show ∀ (a b : ℕ) (la lb : List Unit), la.length = a → lb.length = b →
      (la ++ lb).length = a + b
    intro a b la lb ha hb
    simp [ha, hb]
  · show ∀ m : ℕ, m = 1 → ∃ ps : List Unit, ps.length = m ∧
      ∀ p ∈ ps, ∃ g : Geometry, g = Geometry.hyperbolic
    intro m hm
    exact ⟨[()], by simp [hm], fun p _ => ⟨Geometry.hyperbolic, rfl⟩⟩

/-- The model is genuinely infinite: it has infinitely many distinct manifolds,
infinitely many of which are non-prime connected sums. -/
