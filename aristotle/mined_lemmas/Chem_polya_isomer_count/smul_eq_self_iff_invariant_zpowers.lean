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
