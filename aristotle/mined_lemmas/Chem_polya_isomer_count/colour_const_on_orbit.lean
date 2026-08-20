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

theorem colour_const_on_orbit (g : G) (c : Pos → Sub) (hc : g • c = c) {x y : Pos}
    (h : (orbitRel (Subgroup.zpowers g) Pos) x y) : c x = c y := by
  obtain ⟨k, rfl⟩ := h
  exact (smul_eq_self_iff_invariant_zpowers g c).1 hc k k.2 y

/-- The colourings fixed by `g` are exactly the functions on the set of cycles (orbits) of `g`
acting on the positions. -/
