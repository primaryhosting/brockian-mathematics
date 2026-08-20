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
