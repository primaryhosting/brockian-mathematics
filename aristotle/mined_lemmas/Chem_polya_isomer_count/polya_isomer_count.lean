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
