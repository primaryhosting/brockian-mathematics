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
# Pólya / Burnside counting of substitution isomers

A "skeleton" is a finite set `X` of substitution sites, carrying an action of a finite
symmetry group `G`.  A *substitution pattern* is a function `X → C` assigning to each site
one of finitely many substituents `C`; two patterns describe the same *isomer* exactly when
they differ by a symmetry of the skeleton, i.e. they lie in the same orbit of the induced
action of `G` on `X → C`.

The main result `Chem.polya_isomer_count` states the Pólya/Burnside cycle-index formula:
the number of isomers, times `|G|`, equals `∑ g : G, |C| ^ (number of cycles of g on X)`,
where the number of cycles of `g` is the number of orbits of the cyclic subgroup `⟨g⟩`
acting on `X`.
-/

namespace Chem

-- If `G` acts on the sites `X`, it acts on substitution patterns `X → C` by
-- `(g • f) x = f (g⁻¹ • x)`.
attribute [local instance] arrowAction

variable {G X C : Type*} [Group G] [MulAction G X]

/-- A pattern fixed by `g` is constant along the orbits of the cyclic subgroup `⟨g⟩`. -/

theorem apply_smul_eq_of_mem_fixedBy {g : G} {f : X → C}
    (hf : f ∈ MulAction.fixedBy (X → C) g) {h : G} (hh : h ∈ Subgroup.zpowers g) (x : X) :
    f (h • x) = f x := by
  have hg : g ∈ MulAction.stabilizer G f := hf
  have hmem : h ∈ MulAction.stabilizer G f :=
    (Subgroup.zpowers_le (H := MulAction.stabilizer G f)).mpr hg hh
  have hfix : h • f = f := hmem
  have key : ∀ a : X, f (h⁻¹ • a) = f a := fun a => congrFun hfix a
  have := key (h • x)
  rwa [inv_smul_smul, eq_comm] at this

/-- Patterns fixed by `g` correspond to arbitrary colourings of the set of `⟨g⟩`-orbits
(the cycles of `g`). -/

noncomputable def fixedByEquivCycleColorings (g : G) :
    (MulAction.fixedBy (X → C) g) ≃
      (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X) → C) where
  toFun f := Quotient.lift f.1 (by
    rintro a b hab
    obtain ⟨h, rfl⟩ := hab
    exact apply_smul_eq_of_mem_fixedBy f.2 h.2 b)
  invFun F := ⟨fun x => F (Quotient.mk _ x), by
    have : ∀ x : X, F (Quotient.mk _ (g⁻¹ • x)) = F (Quotient.mk _ x) := by
      intro x
      refine congrArg F (Quotient.sound ?_)
      exact ⟨⟨g⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers g)⟩, rfl⟩
    simp only [MulAction.mem_fixedBy]
    funext x
    simpa [arrowAction] using this x⟩
  left_inv f := by ext x; rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl

variable (G X C)

/-- **Pólya's enumeration theorem / Burnside's lemma for substitution isomers.**
The number of substitution isomers on the skeleton `X` with substituents `C`, i.e. the number
of orbits of the symmetry group `G` on patterns `X → C`, multiplied by `|G|`, equals the sum
over `g : G` of `|C| ^ c(g)`, where `c(g)` is the number of cycles of `g` on the sites, i.e.
the number of orbits of `⟨g⟩` on `X`.  Equivalently, the isomer count is the average
`(1/|G|) ∑_g |C| ^ c(g)` of the cycle index. -/

theorem polya_isomer_count [Fintype G] [Finite X] [Finite C] :
    Nat.card (Quotient (MulAction.orbitRel G (X → C))) * Nat.card G =
      ∑ g : G, Nat.card C ^
        Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)) := by
  classical
  have e := MulAction.sigmaFixedByEquivOrbitsProdGroup G (X → C)
  have h1 : Nat.card (Σ g : G, MulAction.fixedBy (X → C) g) =
      Nat.card (Quotient (MulAction.orbitRel G (X → C))) * Nat.card G := by
    rw [Nat.card_congr e, Nat.card_prod]
  have h2 : Nat.card (Σ g : G, MulAction.fixedBy (X → C) g) =
      ∑ g : G, Nat.card (MulAction.fixedBy (X → C) g) := Nat.card_sigma
  have h3 : ∀ g : G, Nat.card (MulAction.fixedBy (X → C) g) =
      Nat.card C ^ Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)) := by
    intro g
    rw [Nat.card_congr (fixedByEquivCycleColorings (C := C) g), Nat.card_fun]
  rw [← h1, h2]
  exact Finset.sum_congr rfl fun g _ => h3 g

/-- The averaged (rational) form of the Pólya/Burnside cycle-index formula: the number of
substitution isomers is the average over the symmetry group of `|C| ^ c(g)`. -/
