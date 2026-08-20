/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pólya / Burnside isomer count

Counting substitution isomers on a symmetric molecular skeleton: the number of isomers is the
Burnside/Pólya cycle-index average `(1/|G|) ∑_{g ∈ G} |Sub| ^ (number of cycles of g)`.

The key ingredients are Mathlib's Burnside lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, together with the identification of
the colourings fixed by a symmetry `g` with arbitrary functions on the set of cycles of `g`.
-/

namespace Chem

open MulAction

/- The action of the skeleton's symmetry group `G` on colourings (substitution patterns)
`Pos → Sub` is given by `(g • c) x = c (g⁻¹ • x)`. -/
attribute [local instance] arrowAction

section

variable {G Pos Sub : Type*} [Group G] [MulAction G Pos]

/-- The subgroup of symmetries that preserve a given colouring `c`, i.e. the set of `k : G`
with `c (k • x) = c x` for all positions `x`. -/
def colourStabilizer (c : Pos → Sub) : Subgroup G where
  carrier := {k | ∀ x, c (k • x) = c x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha x
    have := ha (a⁻¹ • x)
    rw [smul_inv_smul] at this
    exact this.symm

/-- A colouring is fixed by `g` iff it is invariant under the cyclic group `⟨g⟩`, i.e. iff it is
constant on the cycles of `g`. -/
theorem smul_eq_self_iff_invariant_zpowers (g : G) (c : Pos → Sub) :
    g • c = c ↔ ∀ k ∈ Subgroup.zpowers g, ∀ x, c (k • x) = c x := by
  constructor
  · intro hc
    have key : ∀ a, c (g⁻¹ • a) = c a := fun a => congrFun hc a
    have hg : g ∈ colourStabilizer (Sub := Sub) c := by
      intro x
      have := key (g • x)
      rw [inv_smul_smul] at this
      exact this.symm
    intro k hk
    exact (Subgroup.zpowers_le (H := colourStabilizer (Sub := Sub) c)).2 hg hk
  · intro h
    funext x
    show c (g⁻¹ • x) = c x
    exact h g⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) x

/-- A colouring fixed by `g` is constant on each cycle of `g`. -/
theorem colour_const_on_orbit (g : G) (c : Pos → Sub) (hc : g • c = c) {x y : Pos}
    (h : (orbitRel (Subgroup.zpowers g) Pos) x y) : c x = c y := by
  obtain ⟨k, rfl⟩ := h
  exact (smul_eq_self_iff_invariant_zpowers g c).1 hc k k.2 y

/-- The colourings fixed by `g` are exactly the functions on the set of cycles (orbits) of `g`
acting on the positions. -/
noncomputable def fixedColouringEquiv (g : G) :
    (fixedBy (Pos → Sub) g) ≃ (Quotient (orbitRel (Subgroup.zpowers g) Pos) → Sub) where
  toFun c := Quotient.lift c.1 (fun _ _ h => colour_const_on_orbit g c.1 c.2 h)
  invFun q := ⟨fun x => q (Quotient.mk _ x), by
    refine (smul_eq_self_iff_invariant_zpowers g _).2 (fun k hk x => ?_)
    exact congrArg q (Quotient.sound ⟨⟨k, hk⟩, rfl⟩)⟩
  left_inv c := rfl
  right_inv q := by
    funext x
    induction x using Quotient.inductionOn with
    | _ x => rfl

/-- Pólya's cycle-index count of the colourings fixed by a single symmetry `g`:
it is `|Sub| ^ (number of cycles of g)`. -/
theorem card_fixedBy_colourings [Finite Pos] (g : G) :
    Nat.card (fixedBy (Pos → Sub) g)
      = Nat.card Sub ^ Nat.card (Quotient (orbitRel (Subgroup.zpowers g) Pos)) := by
  have : Finite (Quotient (orbitRel (Subgroup.zpowers g) Pos)) := Quotient.finite _
  rw [Nat.card_congr (fixedColouringEquiv (Sub := Sub) g), Nat.card_fun]

end

section

variable {G Pos Sub : Type*} [Group G] [MulAction G Pos] [Fintype G] [Finite Pos] [Finite Sub]

/-- **Pólya/Burnside isomer count.**  Let a finite symmetry group `G` act on the positions `Pos`
of a molecular skeleton, and let `Sub` be a finite set of substituents.  Two substitution
patterns `Pos → Sub` describe the same isomer when they differ by a symmetry of the skeleton, so
the isomers are the orbits of `G` on the colourings `Pos → Sub`.  Then the number of isomers,
times `|G|`, equals the sum over the group of `|Sub|` raised to the number of cycles of `g` on
the positions — i.e. the number of isomers is the Pólya cycle-index average

`(1/|G|) ∑_{g ∈ G} |Sub| ^ (number of cycles of g)`. -/
theorem polya_isomer_count :
    Nat.card (Quotient (orbitRel G (Pos → Sub))) * Nat.card G
      = ∑ g : G, Nat.card Sub ^ Nat.card (Quotient (orbitRel (Subgroup.zpowers g) Pos)) := by
  classical
  have : Finite (Pos → Sub) := Pi.finite
  letI : ∀ g : G, Fintype (fixedBy (Pos → Sub) g) := fun g => Fintype.ofFinite _
  letI : Fintype (Quotient (orbitRel G (Pos → Sub))) := Fintype.ofFinite _
  have burnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Pos → Sub)
  rw [Nat.card_eq_fintype_card (α := Quotient (orbitRel G (Pos → Sub))),
    Nat.card_eq_fintype_card (α := G), ← burnside]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Nat.card_eq_fintype_card, card_fixedBy_colourings]

/-- The Pólya isomer count written as an average over the group, in `ℚ`. -/
theorem polya_isomer_count_average [Nonempty G] :
    (Nat.card (Quotient (orbitRel G (Pos → Sub))) : ℚ)
      = (1 / (Nat.card G : ℚ)) *
        ∑ g : G, (Nat.card Sub : ℚ) ^ Nat.card (Quotient (orbitRel (Subgroup.zpowers g) Pos)) := by
  have hG : (Nat.card G : ℚ) ≠ 0 := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have h := congrArg (fun n : ℕ => (n : ℚ)) (polya_isomer_count (G := G) (Pos := Pos) (Sub := Sub))
  push_cast at h
  field_simp
  linarith [h]

end

end Chem

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

