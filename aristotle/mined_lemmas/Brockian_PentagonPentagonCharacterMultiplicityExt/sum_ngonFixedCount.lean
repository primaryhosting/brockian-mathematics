/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MulAction

/-!
## The geometric action of the dihedral group on the vertices of an `n`-gon

We model the vertices of a regular `n`-gon by `ZMod n`.  The rotation `r i` moves the vertex
`x` to `x - i` and the reflection `sr i` moves the vertex `x` to `i - x`.
-/

/-- The action of `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon. -/

theorem sum_ngonFixedCount (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, ngonFixedCount n g) = 2 * n := by
  classical
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (α := DihedralGroup n) (β := ZMod n)
  have horb : Fintype.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_ngon_orbits n
  have hcard : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card
  have hfix : ∀ g : DihedralGroup n,
      ngonFixedCount n g = Fintype.card (MulAction.fixedBy (ZMod n) g) := by
    intro g
    simp [ngonFixedCount, Nat.card_eq_fintype_card]
  calc (∑ g : DihedralGroup n, ngonFixedCount n g)
      = ∑ g : DihedralGroup n, Fintype.card (MulAction.fixedBy (ZMod n) g) := by
        exact Finset.sum_congr rfl fun g _ => hfix g
    _ = Fintype.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) *
          Fintype.card (DihedralGroup n) := hB
    _ = 2 * n := by rw [horb, hcard, one_mul]

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Generalizing the `D₅` pentagon computation to arbitrary regular `n`-gons (`n ≠ 0`):
the permutation character `χ` of the action of the dihedral group `DihedralGroup n`
(the symmetry group of the regular `n`-gon, of order `2n`) on the `n` vertices satisfies
`∑ g, χ g = 2n`, i.e. the multiplicity `⟪χ, 1⟫ = |G|⁻¹ ∑ g, χ g` of the trivial character in
`χ` equals `1`. Equivalently, by Burnside's lemma, the action on the vertices has a single
orbit. -/
