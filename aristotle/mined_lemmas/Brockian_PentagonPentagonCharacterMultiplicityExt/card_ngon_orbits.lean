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

theorem card_ngon_orbits (n : ℕ) [NeZero n] :
    Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) = 1 := by
  have : Nonempty (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) :=
    ⟨Quotient.mk _ (0 : ZMod n)⟩
  have hsub : Subsingleton (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) := by
    constructor
    rintro a b
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (DihedralGroup n) y x
        exact Quotient.sound ⟨g, hg⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨hsub, this⟩

/-- **Burnside's lemma** (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) applied to
the vertex action of the dihedral group: the total number of fixed vertices, summed over all
`2n` symmetries of the `n`-gon, is `2n`. -/
