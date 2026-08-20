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
