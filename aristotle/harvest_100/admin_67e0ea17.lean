import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
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

namespace Chem

open MulAction

attribute [local instance] arrowAction

variable {G S C : Type*} [Group G] [MulAction G S]

/-- The number of cycles of the permutation of the skeleton sites `S` induced by a symmetry
`g` of the molecule: the number of orbits of the cyclic group `⟨g⟩` acting on the sites. -/
noncomputable def numCycles (S : Type*) [MulAction G S] (g : G) : ℕ :=
  Nat.card (orbitRel.Quotient (Subgroup.zpowers g) S)

/-- The symmetry group acts on substitution patterns by moving the sites:
`(g • f) s = f (g⁻¹ • s)`. -/
theorem smul_coloring_apply (g : G) (f : S → C) (s : S) : (g • f) s = f (g⁻¹ • s) := rfl

/-- For the identity symmetry every site is its own cycle. -/
theorem numCycles_one [Finite S] : numCycles (G := G) S 1 = Nat.card S := by
  refine Nat.card_congr ?_
  refine Equiv.ofBijective (Quotient.lift id ?_) ⟨?_, ?_⟩
  · rintro a b ⟨h, rfl⟩
    have : (h : G) = 1 := by
      simpa using (Subgroup.zpowers_one_eq_bot (G := G) ▸ h.2 : (h : G) ∈ (⊥ : Subgroup G))
    show ((h : G)) • b = b
    rw [this, one_smul]
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b => exact congrArg (Quotient.mk _) hab
  · intro s
    exact ⟨Quotient.mk _ s, rfl⟩

/-- A substitution pattern fixed by `g` is exactly a function that is constant on the cycles
of `g`, i.e. a function on the set of `⟨g⟩`-orbits of sites. -/
noncomputable def fixedColoringsEquiv (g : G) :
    fixedBy (S → C) g ≃ (orbitRel.Quotient (Subgroup.zpowers g) S → C) where
  toFun f := by
    refine Quotient.lift f.1 ?_
    intro a b hab
    have hst : Subgroup.zpowers g ≤ stabilizer G (f : S → C) := by
      rw [Subgroup.zpowers_le]
      exact f.2
    obtain ⟨h, rfl⟩ := hab
    have : (h⁻¹ : G) • (f : S → C) = f := hst (Subgroup.inv_mem _ h.2)
    calc (f : S → C) ((h : G) • b) = ((h⁻¹ : G) • (f : S → C)) b := by
          show (f : S → C) ((h : G) • b) = (f : S → C) ((h : G)⁻¹⁻¹ • b)
          rw [inv_inv]
      _ = (f : S → C) b := by rw [this]
  invFun F := by
    refine ⟨fun s => F (Quotient.mk _ s), ?_⟩
    have : ∀ s : S, Quotient.mk (orbitRel (Subgroup.zpowers g) S) (g⁻¹ • s)
        = Quotient.mk _ s := by
      intro s
      apply Quotient.sound
      exact ⟨⟨g⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers g)⟩, rfl⟩
    funext s
    show F (Quotient.mk _ (g⁻¹ • s)) = F (Quotient.mk _ s)
    rw [this]
  left_inv f := by ext s; rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | _ s => rfl

/-- The number of substitution patterns left invariant by a symmetry `g` is
`(number of substituents) ^ (number of cycles of g)`. -/
theorem card_fixedBy_colorings [Finite S] [Finite C] (g : G) :
    Nat.card (fixedBy (S → C) g) = Nat.card C ^ numCycles S g := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite C
  rw [Nat.card_congr (fixedColoringsEquiv (C := C) g), numCycles]
  have : Finite (orbitRel.Quotient (Subgroup.zpowers g) S) := Quotient.finite _
  have hf := Fintype.ofFinite (orbitRel.Quotient (Subgroup.zpowers g) S)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fun]

/-- **Pólya / Burnside isomer count.**  Let a finite symmetry group `G` act on the set `S` of
substitution sites of a molecular skeleton, and let `C` be the (finite) set of substituents.
Substitution patterns are functions `S → C`, and two of them describe the same isomer exactly
when they lie in the same `G`-orbit.  Then the number of isomers, multiplied by the order of the
symmetry group, equals the sum over all symmetries `g` of `|C| ^ (number of cycles of g)`;
equivalently, the number of isomers is the average `(1/|G|) ∑_g |C|^{c(g)}`, the value of the
cycle index of `G` at `(|C|, …, |C|)`. -/
theorem polya_isomer_count [Fintype G] [Finite S] [Finite C] :
    Nat.card (orbitRel.Quotient G (S → C)) * Nat.card G =
      ∑ g : G, Nat.card C ^ numCycles S g := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite C
  have hfin : Finite (orbitRel.Quotient G (S → C)) := Quotient.finite _
  have := Fintype.ofFinite (orbitRel.Quotient G (S → C))
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (α := G) (β := S → C)
  calc Nat.card (orbitRel.Quotient G (S → C)) * Nat.card G
      = Fintype.card (orbitRel.Quotient G (S → C)) * Fintype.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    _ = ∑ g : G, Fintype.card (fixedBy (S → C) g) := key.symm
    _ = ∑ g : G, Nat.card C ^ numCycles S g := by
        refine Finset.sum_congr rfl ?_
        intro g _
        rw [← Nat.card_eq_fintype_card, card_fixedBy_colorings]

end Chem

