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

/-- The permutation representation of the dihedral group `D n` on the `n` vertices of a
regular `n`-gon (vertices modelled by `ZMod n`): the rotation `r i` sends a vertex `v` to
`v - i`, and the reflection `sr i` sends `v` to `i - v`. -/
def ngonPerm (n : ℕ) [NeZero n] : DihedralGroup n →* Equiv.Perm (ZMod n) :=
  MonoidHom.mk'
    (fun g => match g with
      | DihedralGroup.r i => ⟨fun v => v - i, fun v => v + i, fun v => by simp, fun v => by simp⟩
      | DihedralGroup.sr i => ⟨fun v => i - v, fun v => i - v, fun v => by simp, fun v => by simp⟩)
    (by
      rintro (i | i) (j | j) <;>
        ext v <;>
        simp [Equiv.Perm.mul_apply, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
          DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;>
        ring)

@[simp] lemma ngonPerm_r (n : ℕ) [NeZero n] (i v : ZMod n) :
    ngonPerm n (DihedralGroup.r i) v = v - i := rfl

@[simp] lemma ngonPerm_sr (n : ℕ) [NeZero n] (i v : ZMod n) :
    ngonPerm n (DihedralGroup.sr i) v = i - v := rfl

/-- The character of the vertex permutation representation: the number of vertices of the
regular `n`-gon fixed by the symmetry `g`. -/
def ngonCharacter (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℕ :=
  (Finset.univ.filter (fun v : ZMod n => ngonPerm n g v = v)).card

/-- The rotations of the `n`-gon contribute `n` fixed vertices in total. -/
lemma sum_ngonCharacter_r (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonCharacter n (DihedralGroup.r i) = n := by
  classical
  have h0 : ngonCharacter n (DihedralGroup.r 0) = n := by
    unfold ngonCharacter
    simp [ZMod.card]
  rw [Finset.sum_eq_single (0 : ZMod n) ?_ ?_]
  · exact h0
  · intro i _ hi
    unfold ngonCharacter
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp only [ngonPerm_r]
    intro h
    exact hi (by linear_combination -h)
  · intro h
    exact absurd (Finset.mem_univ (0 : ZMod n)) h

/-- The reflections of the `n`-gon contribute `n` fixed vertices in total. -/
lemma sum_ngonCharacter_sr (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonCharacter n (DihedralGroup.sr i) = n := by
  classical
  have key : (Finset.univ : Finset (ZMod n)).card =
      ∑ i ∈ (Finset.univ : Finset (ZMod n)),
        (Finset.univ.filter (fun v : ZMod n => v + v = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (v + v))
  have hchar : ∀ i : ZMod n, ngonCharacter n (DihedralGroup.sr i) =
      (Finset.univ.filter (fun v : ZMod n => v + v = i)).card := by
    intro i
    unfold ngonCharacter
    congr 1
    apply Finset.filter_congr
    intro v _
    simp only [ngonPerm_sr]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  calc ∑ i : ZMod n, ngonCharacter n (DihedralGroup.sr i)
      = ∑ i : ZMod n, (Finset.univ.filter (fun v : ZMod n => v + v = i)).card := by
        exact Finset.sum_congr rfl (fun i _ => hchar i)
    _ = (Finset.univ : Finset (ZMod n)).card := key.symm
    _ = n := by simp [ZMod.card]

/-- The dihedral group `D n` as a disjoint union of rotations and reflections. -/
def dihedralEquivSum (n : ℕ) : ZMod n ⊕ ZMod n ≃ DihedralGroup n where
  toFun := fun x => match x with
    | Sum.inl j => DihedralGroup.r j
    | Sum.inr j => DihedralGroup.sr j
  invFun := fun g => match g with
    | DihedralGroup.r j => Sum.inl j
    | DihedralGroup.sr j => Sum.inr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

lemma sum_dihedral {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n]
    (f : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, f g =
      (∑ i : ZMod n, f (DihedralGroup.r i)) + ∑ i : ZMod n, f (DihedralGroup.sr i) := by
  rw [← Equiv.sum_comp (dihedralEquivSum n) f, Fintype.sum_sum_type]
  rfl

/-- Total number of fixed vertices, summed over all `2n` symmetries of the regular `n`-gon. -/
lemma sum_ngonCharacter (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonCharacter n g = 2 * n := by
  classical
  rw [sum_dihedral n (ngonCharacter n), sum_ngonCharacter_r, sum_ngonCharacter_sr]
  ring

/--
**Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the `D 5` (pentagon) computation to every regular `n`-gon: for the
permutation representation of the dihedral group `D n` on the `n` vertices of the regular
`n`-gon, the multiplicity of the trivial representation, i.e. the inner product
`⟪χ, 1⟫ = (1 / |D n|) * ∑_{g} χ(g)`, equals `1` (the vertex action is transitive, so there is
exactly one orbit).
-/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (1 / (Fintype.card (DihedralGroup n) : ℚ)) *
        ∑ g : DihedralGroup n, (ngonCharacter n g : ℚ) = 1 := by
  classical
  have hcard : (Fintype.card (DihedralGroup n) : ℚ) = 2 * n := by
    rw [DihedralGroup.card]
    push_cast
    ring
  have hsum : ∑ g : DihedralGroup n, (ngonCharacter n g : ℚ) = 2 * n := by
    have := sum_ngonCharacter n
    have : ((∑ g : DihedralGroup n, ngonCharacter n g : ℕ) : ℚ) = ((2 * n : ℕ) : ℚ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) this
    push_cast at this
    simpa using this
  have hn : (n : ℚ) ≠ 0 := by
    have := NeZero.ne n
    exact_mod_cast this
  rw [hcard, hsum]
  field_simp

/-- The pentagon case `n = 5`: the ten symmetries of the regular pentagon fix ten vertices
in total, so the trivial representation occurs with multiplicity one. -/
theorem pentagon_character_multiplicity :
    (1 / (Fintype.card (DihedralGroup 5) : ℚ)) *
        ∑ g : DihedralGroup 5, (ngonCharacter 5 g : ℚ) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5

end Brockian

