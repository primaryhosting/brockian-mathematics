/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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
lemma card_filter_fixed (x : X) :
    (Finset.univ.filter fun g : G => g • x = x).card
      = Fintype.card (MulAction.stabilizer G x) := by
  rw [Fintype.card_subtype]
  rfl

omit [Fintype X] in
/-- All "hitting sets" `{g | g • x = y}` (for `y` in the orbit of `x`) have the cardinality
of the stabilizer of `x`. -/
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
theorem sing_uniform_of_transitive (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y : X) :
    Fintype.card X * (Finset.univ.filter fun g : G => g • x = y).card = Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := htrans x y
  rw [card_filter_smul_eq_card_stabilizer hg₀]
  have horb : MulAction.orbit G x = (Set.univ : Set X) := by
    ext z
    simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
    exact htrans x z
  haveI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
  have hcard : Fintype.card (MulAction.orbit G x) = Fintype.card X := by
    simpa using Fintype.card_congr (Equiv.setCongr horb)
  rw [← hcard]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- Equidistribution: the hitting sets have equal cardinality for all targets. -/
theorem card_filter_smul_const (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y₁ y₂ : X) :
    (Finset.univ.filter fun g : G => g • x = y₁).card
      = (Finset.univ.filter fun g : G => g • x = y₂).card := by
  have h1 := sing_uniform_of_transitive htrans x y₁
  have h2 := sing_uniform_of_transitive htrans x y₂
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_left hX (h1.trans h2.symm)

end Brockian.EquidistributionUniformity

