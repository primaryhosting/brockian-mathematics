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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The *singular transport set* of the pair `(x, y)`: the set of group elements that move the
point `x` to the point `y`. -/
def transportSet (G : Type*) {X : Type*} [Group G] [MulAction G X] (x y : X) : Set G :=
  {g : G | g • x = y}

/-- The *singular count* of a pair `(x, y)`: the number of group elements moving `x` to `y`. -/
noncomputable def singCount (G : Type*) {X : Type*} [Group G] [MulAction G X] (x y : X) : ℕ :=
  Nat.card (transportSet G x y)

@[simp] lemma mem_transportSet {x y : X} {g : G} : g ∈ transportSet G x y ↔ g • x = y := Iff.rfl

/-- Whenever it is nonempty, the transport set of `(x, y)` is a left coset of the stabilizer of
`x`, hence is in bijection with that stabilizer. -/
lemma transportSet_equiv_stabilizer {x y : X} {g₀ : G} (hg₀ : g₀ • x = y) :
    Nonempty (transportSet G x y ≃ stabilizer G x) := by
  refine ⟨⟨fun g => ⟨g₀⁻¹ * (g : G), ?_⟩, fun h => ⟨g₀ * (h : G), ?_⟩, ?_, ?_⟩⟩
  · have hg : (g : G) • x = y := g.2
    simp [MulAction.mem_stabilizer_iff, mul_smul, hg, ← hg₀]
  · have hh : (h : G) • x = x := h.2
    simp [mem_transportSet, mul_smul, hh, hg₀]
  · rintro ⟨g, hg⟩
    ext
    simp
  · rintro ⟨h, hh⟩
    ext
    simp

/-- The singular count of `(x, y)` equals the cardinality of the stabilizer of `x`, for a
transitive action. -/
lemma singCount_eq_card_stabilizer [IsPretransitive G X] (x y : X) :
    singCount G x y = Nat.card (stabilizer G x) := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  exact Nat.card_congr (transportSet_equiv_stabilizer hg₀).some

/-- **Equidistribution uniformity for transitive actions.**

If a group `G` acts transitively on `X`, then the number of group elements carrying a given point
`x` to a given point `y` does not depend on the chosen pair `(x, y)` (uniformity), and this common
count multiplied by the number of points of `X` is the order of `G`.

In particular, for finite `G` and `X` the count is exactly `|G| / |X|`. -/
theorem sing_uniform_of_transitive [IsPretransitive G X] (x y x' y' : X) :
    singCount G x y = singCount G x' y' ∧ singCount G x y * Nat.card X = Nat.card G := by
  have hxx' : Nat.card (stabilizer G x) = Nat.card (stabilizer G x') := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x x'
    subst hg
    exact Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel
      (MulAction.mem_orbit x g)).toEquiv.symm
  refine ⟨by rw [singCount_eq_card_stabilizer, singCount_eq_card_stabilizer, hxx'], ?_⟩
  rw [singCount_eq_card_stabilizer, ← MulAction.index_stabilizer_of_transitive G x]
  exact Subgroup.card_mul_index _

/-- Finite form: for a transitive action of a finite group, the number of elements carrying `x`
to `y` is exactly `Nat.card G / Nat.card X`. -/
theorem singCount_eq_div_of_transitive [Finite G] [IsPretransitive G X] (x y : X) :
    singCount G x y = Nat.card G / Nat.card X := by
  have h := (sing_uniform_of_transitive (G := G) x y x y).2
  have hX : 0 < Nat.card X := Nat.card_pos_iff.2 ⟨⟨x⟩, Finite.of_surjective
    (fun g : G => g • x) (fun z => MulAction.exists_smul_eq G x z)⟩
  rw [← h, Nat.mul_div_cancel _ hX]

/-! ### Sanity checks: the hypotheses are satisfiable and the counts are the expected ones. -/

/-- The hypothesis of transitivity is satisfiable: the symmetric group acts transitively. -/
example : MulAction.IsPretransitive (Equiv.Perm (Fin 3)) (Fin 3) := inferInstance

/-- For the left regular action of a group on itself the uniform count is `1`. -/
example (G : Type*) [Group G] (x y : G) : singCount G x y = 1 := by
  have h : transportSet G x y = {y * x⁻¹} := by
    ext g
    simp only [transportSet, Set.mem_setOf_eq, smul_eq_mul, Set.mem_singleton_iff,
      eq_mul_inv_iff_mul_eq]
  rw [singCount, h, Nat.card_coe_set_eq, Set.ncard_singleton]


end EquidistributionUniformity
end Brockian

