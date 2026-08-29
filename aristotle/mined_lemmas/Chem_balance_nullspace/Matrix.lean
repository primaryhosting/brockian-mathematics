/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/

theorem Matrix.exists_pos_int_nullVector_iff {E S : Type*} [Fintype S] (A : Matrix E S ℤ) :
    (∃ x : S → ℝ, (∀ s, 0 < x s) ∧ (A.map (Int.cast : ℤ → ℝ)).mulVec x = 0) ↔
      (∃ n : S → ℤ, (∀ s, 0 < n s) ∧ A.mulVec n = 0) := by
  constructor
  · rintro ⟨x, hxpos, hx⟩
    have hx' : ∀ e, ∑ s, (A e s : ℝ) * x s = 0 := by
      intro e
      have := congrFun hx e
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
    obtain ⟨y, hypos, hy⟩ := exists_pos_rat_null A x hxpos hx'
    obtain ⟨n, hnpos, hn⟩ := exists_pos_int_null A y hypos hy
    exact ⟨n, hnpos, funext fun e => by simpa [Matrix.mulVec, dotProduct] using hn e⟩
  · rintro ⟨n, hnpos, hn⟩
    refine ⟨fun s => (n s : ℝ), fun s => Int.cast_pos.mpr (hnpos s), funext fun e => ?_⟩
    have hne := congrFun hn e
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hne ⊢
    have hcast : ((∑ s, A e s * n s : ℤ) : ℝ) = 0 := by exact_mod_cast hne
    push_cast at hcast
    simpa using hcast

/-! ## Chemical reactions -/

/-- A chemical reaction: `atoms e s` is the number of atoms of element `e` in one formula
unit of species `s`, and `isProduct s` says whether the species `s` appears on the product
side of the reaction arrow (the remaining species being reactants). -/
structure Reaction (Elem Species : Type*) where
  /-- number of atoms of element `e` in one formula unit of species `s` -/
  atoms : Elem → Species → ℕ
  /-- `true` for products, `false` for reactants -/
  isProduct : Species → Bool

/-- The stoichiometric matrix of a reaction: atom counts, taken positively for products and
negatively for reactants. -/
