/-!
# Twin-unit deletion masks on the canonical sieve blocks

This module restricts the lane-coordinate equivalence from
`SieveSpectrumBlocks` to the actual twin-unit predicate. It proves that every
twin-admissible residue has one of the three modulo-15 lanes, gives the exact
equivalence between surviving wheel sites and surviving block coordinates,
and defines the corresponding deletion mask on each potential path.
-/

import Mathlib
import Brockian.SieveSpectrumBlocks

set_option autoImplicit false

namespace Brockian.SieveSpectrumDeletion

open Brockian.SieveSpectrumBlocks

noncomputable section

/-- Actual twin admissibility in the complete wheel. -/
def TwinVertex (Q : Nat) [NeZero Q] (a : ZMod (15 * Q)) : Prop :=
  IsUnit a ∧ IsUnit (a + 2)

/-- Modulo 15, the twin-unit residues are exactly the three canonical lanes. -/
theorem twin_lanes_mod15 (a : ZMod 15) :
    (IsUnit a ∧ IsUnit (a + 2)) ↔
      a = lane15 0 ∨ a = lane15 1 ∨ a = lane15 2 := by
  decide +revert

private theorem crt15Q_two
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    crt15Q Q h15 (2 : ZMod (15 * Q)) =
      ((2 : ZMod 15), (2 : ZMod Q)) := by
  calc
    crt15Q Q h15 (2 : ZMod (15 * Q)) =
        (2 : ZMod 15 × ZMod Q) := map_natCast (crt15Q Q h15) 2
    _ = ((2 : ZMod 15), (2 : ZMod Q)) := by rfl

/-- Every actual twin vertex lies on one of the canonical modulo-15 lanes. -/
theorem twinVertex_isLaneSite
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (a : ZMod (15 * Q)) (ha : TwinVertex Q a) :
    IsLaneSite Q h15 a := by
  let cred := crt15Q Q h15
  have huPair : IsUnit (cred a) := IsUnit.map cred.toRingHom ha.1
  have hu0 : IsUnit (cred a).1 :=
    IsUnit.map (RingHom.fst (ZMod 15) (ZMod Q)) huPair
  have huPair2 : IsUnit (cred (a + 2)) :=
    IsUnit.map cred.toRingHom ha.2
  have hmap : cred (a + 2) = cred a + ((2 : ZMod 15), (2 : ZMod Q)) := by
    rw [map_add, crt15Q_two]
  have hu2 : IsUnit ((cred a).1 + 2) := by
    rw [hmap] at huPair2
    exact IsUnit.map (RingHom.fst (ZMod 15) (ZMod Q)) huPair2
  rcases (twin_lanes_mod15 (cred a).1).mp ⟨hu0, hu2⟩ with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

/-- Twin-admissible sites in canonical block coordinates. -/
def BlockSite (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :=
  {x : ZMod Q × Fin 3 // TwinVertex Q (blockVertex Q h15 x.1 x.2)}

/-- Twin-admissible sites in the original wheel coordinates. -/
def WheelSite (Q : Nat) [NeZero Q] :=
  {a : ZMod (15 * Q) // TwinVertex Q a}

/-- Forget the canonical block coordinates. -/
def blockSiteMap
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    BlockSite Q h15 -> WheelSite Q := fun x =>
  ⟨blockVertex Q h15 x.val.fst x.val.snd, x.property⟩

/-- The canonical block map is a bijection on actual twin vertices. -/
theorem blockSiteMap_bijective
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    Function.Bijective (blockSiteMap Q h15) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply blockVertex_injective Q h15
    exact congrArg Subtype.val hxy
  · intro y
    have hlane := twinVertex_isLaneSite Q h15 y.1 y.2
    rcases existsUnique_blockVertex_of_lane Q h15 y.1 hlane with
      ⟨x, hx, _⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa [hx] using y.2
    · apply Subtype.ext
      exact hx

/-- Exact equivalence between surviving block sites and surviving wheel sites. -/
def blockSiteEquiv
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q) :
    BlockSite Q h15 ≃ WheelSite Q :=
  Equiv.ofBijective (blockSiteMap Q h15) (blockSiteMap_bijective Q h15)

/-- Adjacency is preserved and reflected on the surviving-site equivalence. -/
theorem blockSite_wheelAdj_iff
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (x y : BlockSite Q h15) :
    WheelAdj (blockSiteMap Q h15 x).1 (blockSiteMap Q h15 y).1 ↔
      BlockAdj x.1 y.1 := by
  exact wheelAdj_iff_blockAdj Q h15 x.1 y.1

/-- Surviving lanes in the potential block indexed by `b`. -/
noncomputable def wheelMask
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (b : ZMod Q) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter
    (fun j => TwinVertex Q (blockVertex Q h15 b j))

@[simp] theorem mem_wheelMask
    (Q : Nat) [NeZero Q] (h15 : Nat.Coprime 15 Q)
    (b : ZMod Q) (j : Fin 3) :
    j ∈ wheelMask Q h15 b ↔
      TwinVertex Q (blockVertex Q h15 b j) := by
  classical
  simp [wheelMask]

end

end Brockian.SieveSpectrumDeletion
