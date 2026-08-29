/-
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

open MulAction

/-- The set of group elements moving `x` to `y` is a left coset of the stabilizer of `x`,
hence has the same cardinality as the stabilizer, provided some element does move `x` to `y`. -/

theorem sing_uniform_ratio_of_transitive {G X : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] [DecidableEq X] [MulAction.IsPretransitive G X] (x y : X) :
    ((Finset.univ.filter fun g : G => g • x = y).card : ℝ) / (Fintype.card G : ℝ)
      = 1 / (Fintype.card X : ℝ) := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := G))
  have hX : (Fintype.card X : ℝ) ≠ 0 := by
    have : Nonempty X := ⟨x⟩
    exact_mod_cast (Fintype.card_ne_zero (α := X))
  have h := sing_uniform_of_transitive (G := G) x y
  have h' : ((Finset.univ.filter fun g : G => g • x = y).card : ℝ) * (Fintype.card X : ℝ)
      = (Fintype.card G : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  field_simp
  linarith [h']

/-- Hypothesis form of `sing_uniform_of_transitive`: transitivity of the action is given as an
ordinary hypothesis `htrans` rather than as a typeclass instance. -/
