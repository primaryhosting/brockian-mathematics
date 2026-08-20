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
# Equidistribution / uniformity for transitive group actions

For a finite group `G` acting transitively on a finite type `X`, the "hitting sets"
`{g : G | g • x = y}` all have the same cardinality, namely `|G| / |X|`.
Equivalently, if `g` is drawn uniformly at random from `G`, then `g • x` is uniformly
distributed on `X`.

The main result `sing_uniform_of_transitive` is stated unconditionally (beyond
transitivity of the action): no auxiliary uniformity hypothesis is assumed.
-/

namespace Brockian.EquidistributionUniformity

open scoped Pointwise

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The set of group elements sending `x` to `x` is exactly the stabilizer, as a `Finset`. -/

lemma card_filter_smul_eq_card_stabilizer {x y : X} {g₀ : G} (hg₀ : g₀ • x = y) :
    (Finset.univ.filter fun g : G => g • x = y).card
      = Fintype.card (MulAction.stabilizer G x) := by
  rw [← card_filter_fixed (G := G) x]
  refine Finset.card_bij' (fun g _ => g₀⁻¹ * g) (fun g _ => g₀ * g) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ← hg₀, inv_smul_smul]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, hg₀]
  · intro g _
    simp [mul_inv_cancel_left]
  · intro g _
    simp [inv_mul_cancel_left]

/-- **Uniformity of a transitive action.**  If a finite group `G` acts transitively on a
finite type `X`, then for every pair `x y : X` the number of group elements carrying `x`
to `y` is `|G| / |X|`; precisely, `|X| * #{g | g • x = y} = |G|`.  In particular the
distribution of `g • x` for uniformly random `g` is the uniform distribution on `X`. -/
