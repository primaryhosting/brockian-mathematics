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
