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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

-- The skeleton symmetry group acts on colourings (substitution patterns)
-- `P → C` of the positions `P` by `(g • f) p = f (g⁻¹ • p)`.
attribute [local instance] arrowAction

variable {G P C : Type*} [Group G] [MulAction G P]

/-- The subgroup of symmetries that leave a given colouring `f` pointwise unchanged,
in the sense that `f (h • p) = f p` for every position `p`. -/
def colourStab (f : P → C) : Subgroup G where
  carrier := {h | ∀ p, f (h • p) = f p}
  one_mem' := by intro p; simp
  mul_mem' := by
    intro a b ha hb p
    rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha p
    have := ha (a⁻¹ • p)
    rwa [smul_inv_smul, eq_comm] at this

/-- A colouring fixed by `g` is constant along the `⟨g⟩`-orbits of the positions. -/
lemma constant_on_zpowers_orbits {g : G} {f : P → C} (hf : g • f = f)
    (h : G) (hh : h ∈ Subgroup.zpowers g) (p : P) : f (h • p) = f p := by
  have hg : g ∈ colourStab (C := C) f := by
    intro q
    have : f (g⁻¹ • (g • q)) = f (g • q) := congrFun hf (g • q)
    rwa [inv_smul_smul, eq_comm] at this
  exact (Subgroup.zpowers_le.mpr hg) hh p

/-- **Pólya's key counting step.**  The colourings fixed by a symmetry `g` are exactly the
colourings of the set of cycles (`⟨g⟩`-orbits) of `g` on the positions. -/
def fixedColouringEquiv (g : G) :
    (MulAction.fixedBy (P → C) g) ≃
      (Quotient (MulAction.orbitRel (Subgroup.zpowers g) P) → C) where
  toFun f := Quotient.lift (fun p => (f : P → C) p) <| by
    intro a b hab
    obtain ⟨⟨h, hh⟩, rfl⟩ := (MulAction.orbitRel_apply.mp hab)
    exact constant_on_zpowers_orbits f.2 h hh b
  invFun F := by
    refine ⟨fun p => F (Quotient.mk _ p), ?_⟩
    funext p
    show F (Quotient.mk _ (g⁻¹ • p)) = F (Quotient.mk _ p)
    congr 1
    exact Quotient.sound (MulAction.orbitRel_apply.mpr
      ⟨⟨g⁻¹, inv_mem (Subgroup.mem_zpowers g)⟩, rfl⟩)
  left_inv f := by ext p; rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-- The number of colourings fixed by a symmetry `g` is `|C|` to the power of the number of
cycles of `g`. -/
theorem card_fixedBy_eq_pow_cycles [Finite P] (g : G) :
    Nat.card (MulAction.fixedBy (P → C) g)
      = Nat.card C ^ Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) P)) := by
  rw [Nat.card_congr (fixedColouringEquiv (C := C) g), Nat.card_fun]

/-- **Pólya / Burnside isomer count.**

Let a finite symmetry group `G` act on the set `P` of substitution positions of a molecular
skeleton, and let `C` be the (finite) set of available substituents.  Two substitution patterns
`P → C` describe the same isomer exactly when they lie in the same `G`-orbit.  Then the number of
isomers, multiplied by the order of the symmetry group, equals the Pólya cycle-index sum
`∑_{g ∈ G} |C| ^ c(g)`, where `c(g)` is the number of cycles (`⟨g⟩`-orbits) of `g` on the
positions.

This is Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) combined
with the evaluation of the fixed-point counts (`card_fixedBy_eq_pow_cycles`). -/
theorem polya_isomer_count [Fintype G] [Finite P] [Finite C] :
    Nat.card (Quotient (MulAction.orbitRel G (P → C))) * Nat.card G
      = ∑ g : G, Nat.card C ^ Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) P)) := by
  classical
  haveI : Finite (P → C) := Pi.finite
  haveI : Fintype (Quotient (MulAction.orbitRel G (P → C))) := Fintype.ofFinite _
  haveI : ∀ a : G, Fintype (MulAction.fixedBy (P → C) a) := fun _ => Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (P → C)
  simp only [← Nat.card_eq_fintype_card] at hB
  rw [← hB]
  exact Finset.sum_congr rfl fun g _ => card_fixedBy_eq_pow_cycles g

/-- The isomer count as the Pólya cycle-index **average** over the symmetry group. -/
theorem polya_isomer_count_eq_average [Fintype G] [Finite P] [Finite C] :
    Nat.card (Quotient (MulAction.orbitRel G (P → C)))
      = (∑ g : G, Nat.card C ^ Nat.card (Quotient (MulAction.orbitRel (Subgroup.zpowers g) P)))
          / Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rw [← polya_isomer_count, Nat.mul_div_cancel _ hpos]

end Chem

