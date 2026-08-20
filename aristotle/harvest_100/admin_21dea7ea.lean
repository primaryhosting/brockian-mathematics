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
def ngonSMul (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r i, x => x - i
  | .sr i, x => i - x

instance ngonHasSMul (n : ℕ) : SMul (DihedralGroup n) (ZMod n) := ⟨ngonSMul n⟩

@[simp]
theorem r_smul (n : ℕ) (i x : ZMod n) : (DihedralGroup.r i) • x = x - i := rfl

@[simp]
theorem sr_smul (n : ℕ) (i x : ZMod n) : (DihedralGroup.sr i) • x = i - x := rfl

instance ngonMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  one_smul x := by
    show ngonSMul n (DihedralGroup.r 0) x = x
    simp [ngonSMul]
  mul_smul g h x := by
    rcases g with i | i <;> rcases h with j | j <;> simp <;> ring

/-- The action of the dihedral group on the vertices of the `n`-gon is transitive
(for `n ≠ 0`): the rotations already act transitively. -/
instance ngonIsPretransitive (n : ℕ) [NeZero n] :
    MulAction.IsPretransitive (DihedralGroup n) (ZMod n) where
  exists_smul_eq x y := ⟨DihedralGroup.r (x - y), by simp⟩

/-- The permutation character of the vertex representation of `DihedralGroup n`:
the number of vertices of the `n`-gon fixed by the symmetry `g`. -/
noncomputable def ngonFixedCount (n : ℕ) (g : DihedralGroup n) : ℕ :=
  Nat.card (MulAction.fixedBy (ZMod n) g)

/-- There is exactly one orbit of the dihedral group on the vertices of the `n`-gon. -/
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
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, ngonFixedCount n g) = 2 * n ∧
      ((Nat.card (DihedralGroup n) : ℚ))⁻¹ *
        (∑ g : DihedralGroup n, (ngonFixedCount n g : ℚ)) = 1 ∧
      Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n)) = 1 := by
  classical
  have hsum := sum_ngonFixedCount n
  have hcard : Nat.card (DihedralGroup n) = 2 * n := by
    rw [Nat.card_eq_fintype_card]; exact DihedralGroup.card
  refine ⟨hsum, ?_, card_ngon_orbits n⟩
  have hQ : (∑ g : DihedralGroup n, (ngonFixedCount n g : ℚ)) = ((2 * n : ℕ) : ℚ) := by
    rw [← hsum]
    push_cast
    rfl
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [hQ, hcard]
  push_cast
  field_simp

/-- The pentagon case `n = 5`: the `10` symmetries of the regular pentagon fix `10` vertices
in total, so the trivial character occurs with multiplicity one in the vertex permutation
character of `D₅`. -/
theorem pentagon_character_multiplicity :
    (∑ g : DihedralGroup 5, ngonFixedCount 5 g) = 10 :=
  sum_ngonFixedCount 5

end Brockian

