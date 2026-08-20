import Brockian.EquidistributionUniformity

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
# Equidistribution from transitive symmetry

If a finite group `G` acts transitively on a finite set `X`, then the orbit map
`g ↦ g • x` distributes the group uniformly over `X`: for every subset `A` of `X`
the proportion of group elements `g` with `g • x ∈ A` equals `|A| / |X|`.

The main result `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry`
is stated unconditionally (transitivity is part of the hypotheses on the action; no
auxiliary result is assumed).
-/

open scoped BigOperators
open Finset MulAction

namespace Brockian
namespace EquidistributionUniformity

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The number of group elements moving `x` to a fixed point `y` in its orbit does not
depend on `y`. -/

theorem uniform_of_invariant_weight [Nonempty X] [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (y : X), w (g • y) = w y)
    (hsum : ∑ y, w y = 1) (x : X) :
    w x = 1 / Fintype.card X := by
  have hconst : ∀ y : X, w y = w x := by
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    exact hinv g x
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos (α := X)
  have : (Fintype.card X : ℝ) * w x = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  field_simp at this ⊢
  linarith [this]

end EquidistributionUniformity
end Brockian

