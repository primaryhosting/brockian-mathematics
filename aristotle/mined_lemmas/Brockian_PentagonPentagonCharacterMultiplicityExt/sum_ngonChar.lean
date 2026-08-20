import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
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

namespace Brockian

open MulAction DihedralGroup

/-! ## The action of the dihedral group on the vertices of the regular `n`-gon -/

/-- The symmetry action of `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon:
the rotation `r i` sends a vertex `x` to `x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

theorem sum_ngonChar (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g = Fintype.card (DihedralGroup n) := by
  haveI : Fintype (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) := Quotient.fintype _
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (ZMod n)
  rw [ngon_orbits_card n, one_mul] at hburnside
  rw [← hburnside]
  exact Finset.sum_congr rfl fun g _ => Nat.card_eq_fintype_card

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the pentagon (`D₅`) computation to arbitrary regular `n`-gons: for every `n ≥ 1`,
the multiplicity of the trivial character in the permutation character `ngonChar n` of the vertex
representation of the dihedral group `DihedralGroup n` — that is, the character inner product
`⟪χ, 1⟫ = |G|⁻¹ ∑_{g ∈ G} χ(g)` — is exactly `1`, because the action on the vertices of the
`n`-gon is transitive (Burnside's lemma,
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`). -/
