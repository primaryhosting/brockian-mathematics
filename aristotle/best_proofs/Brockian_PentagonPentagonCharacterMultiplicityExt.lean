import Mathlib

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

/-!
# Character multiplicities for the vertex representation of the dihedral group

This file generalizes the classical `D₅` (pentagon) representation-theoretic computation to
arbitrary regular `n`-gons.

The symmetry group of the regular `n`-gon is `DihedralGroup n`, acting on the vertex set
`ZMod n`.  We define

* `Brockian.vertexAct` : the action of `DihedralGroup n` on the vertices `ZMod n`;
* `Brockian.permChar`  : the character of the permutation (vertex) representation, i.e. the
  number of vertices fixed by a group element;
* `Brockian.dihedralChar n k` : the character of the two–dimensional representation `ρ_k`
  of `DihedralGroup n` (rotation by `2πk/n`), namely `r i ↦ 2 cos (2πki/n)`, `sr i ↦ 0`;
* `Brockian.charMult` : the multiplicity `⟨χ_perm, χ⟩ = (1/|G|) ∑_g χ_perm(g) χ(g)`.

The main theorem `Brockian.PentagonPentagonCharacterMultiplicityExt` states that every such
two–dimensional character occurs in the vertex representation with multiplicity exactly `1`,
for every `n` and every `k`.  Auxiliary results compute the multiplicity of the trivial
character (`1`, i.e. Burnside's lemma for the transitive vertex action) and of the sign
character (`0`).
-/

namespace Brockian

open DihedralGroup

/-- The action of the symmetry group of the regular `n`-gon on its vertex set `ZMod n`:
the rotation `r i` sends `v` to `v - i`, and the reflection `sr i` sends `v` to `i - v`. -/
def vertexAct (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | r i, v => v - i
  | sr i, v => i - v

@[simp] lemma vertexAct_r (n : ℕ) (i v : ZMod n) : vertexAct n (r i) v = v - i := rfl

@[simp] lemma vertexAct_sr (n : ℕ) (i v : ZMod n) : vertexAct n (sr i) v = i - v := rfl

lemma vertexAct_one (n : ℕ) (v : ZMod n) : vertexAct n 1 v = v := by
  show v - 0 = v
  simp

lemma vertexAct_mul (n : ℕ) (g h : DihedralGroup n) (v : ZMod n) :
    vertexAct n (g * h) v = vertexAct n g (vertexAct n h v) := by
  cases g <;> cases h <;>
    simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr, vertexAct] <;> ring

/-- The vertex action makes `ZMod n` a `DihedralGroup n`-set. -/
instance vertexMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul g v := vertexAct n g v
  one_smul := vertexAct_one n
  mul_smul := vertexAct_mul n

/-- The character of the permutation representation on the vertices of the regular `n`-gon:
the number of vertices fixed by `g`. -/
def permChar (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℕ :=
  (Finset.univ.filter fun v : ZMod n => vertexAct n g v = v).card

/-- The character of the two-dimensional representation `ρ_k` of the dihedral group. -/
noncomputable def dihedralChar (n : ℕ) (k : ℤ) : DihedralGroup n → ℝ
  | r i => 2 * Real.cos (2 * Real.pi * (k : ℝ) * (i.val : ℝ) / (n : ℝ))
  | sr _ => 0

@[simp] lemma dihedralChar_r (n : ℕ) (k : ℤ) (i : ZMod n) :
    dihedralChar n k (r i) = 2 * Real.cos (2 * Real.pi * (k : ℝ) * (i.val : ℝ) / (n : ℝ)) := rfl

@[simp] lemma dihedralChar_sr (n : ℕ) (k : ℤ) (i : ZMod n) : dihedralChar n k (sr i) = 0 := rfl

/-- The trivial character of the dihedral group. -/
def trivialChar (n : ℕ) : DihedralGroup n → ℝ := fun _ => 1

/-- The sign character of the dihedral group: `1` on rotations, `-1` on reflections. -/
def signChar (n : ℕ) : DihedralGroup n → ℝ
  | r _ => 1
  | sr _ => -1

/-- The multiplicity of a (real) character `chi` in the vertex representation of the
regular `n`-gon, i.e. the inner product `(1/|G|) ∑_g χ_perm(g) chi(g)`. -/
noncomputable def charMult (n : ℕ) [NeZero n] (chi : DihedralGroup n → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ g : DihedralGroup n, (permChar n g : ℝ) * chi g

/-- Splitting a sum over the dihedral group into rotations and reflections. -/
lemma sum_dihedral {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n] (f : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, f g = (∑ i : ZMod n, f (r i)) + ∑ i : ZMod n, f (sr i) := by
  classical
  let e : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n :=
    { toFun := fun s => Sum.casesOn s (fun j => r j) (fun j => sr j)
      invFun := fun g => DihedralGroup.casesOn g (fun j => Sum.inl j) (fun j => Sum.inr j)
      left_inv := by rintro (x | x) <;> rfl
      right_inv := by rintro (x | x) <;> rfl }
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  rfl

lemma permChar_r (n : ℕ) [NeZero n] (i : ZMod n) :
    permChar n (r i) = if i = 0 then n else 0 := by
  classical
  by_cases hi : i = 0
  · subst hi
    have huniv : (Finset.univ.filter fun v : ZMod n => vertexAct n (r (0 : ZMod n)) v = v)
        = Finset.univ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, vertexAct_r, sub_zero]
    rw [if_pos rfl, permChar, huniv, Finset.card_univ, ZMod.card]
  · simp only [permChar, hi, if_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp only [vertexAct_r]
    intro h
    exact hi (by linear_combination -h)

@[simp] lemma permChar_one (n : ℕ) [NeZero n] : permChar n 1 = n := by
  have h : (1 : DihedralGroup n) = r 0 := rfl
  rw [h, permChar_r, if_pos rfl]

/-- Summed over all reflections, the number of fixed vertices is `n`. -/
lemma sum_permChar_sr (n : ℕ) [NeZero n] : ∑ i : ZMod n, permChar n (sr i) = n := by
  classical
  have key : ∀ i : ZMod n,
      (Finset.univ.filter fun v : ZMod n => vertexAct n (sr i) v = v)
        = Finset.univ.filter fun v : ZMod n => v + v = i := by
    intro i
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vertexAct_sr]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  calc ∑ i : ZMod n, permChar n (sr i)
      = ∑ i : ZMod n, (Finset.univ.filter fun v : ZMod n => v + v = i).card :=
        Finset.sum_congr rfl fun i _ => by rw [permChar, key i]
    _ = (Finset.univ : Finset (ZMod n)).card := by
        rw [← Finset.card_eq_sum_card_fiberwise (f := fun v : ZMod n => v + v)]
        intro x _
        exact Finset.mem_univ _
    _ = n := by simp [ZMod.card]

/-- **Main theorem.**  Generalizing the pentagon (`D₅`) computation to the regular `n`-gon:
each two-dimensional character `χ_k` of `DihedralGroup n` occurs in the permutation
representation on the vertices with multiplicity exactly `1`. -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] (k : ℤ) :
    charMult n (dihedralChar n k) = 1 := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hsr : ∑ i : ZMod n, (permChar n (sr i) : ℝ) * dihedralChar n k (sr i) = 0 := by
    simp
  have hr : ∑ i : ZMod n, (permChar n (r i) : ℝ) * dihedralChar n k (r i) = 2 * (n : ℝ) := by
    rw [Finset.sum_eq_single (0 : ZMod n)]
    · have hc : 2 * Real.pi * (k : ℝ) * (((0 : ZMod n).val : ℝ)) / (n : ℝ) = 0 := by simp
      rw [permChar_r, if_pos rfl, dihedralChar_r, hc, Real.cos_zero]
      ring
    · intro b _ hb
      rw [permChar_r, if_neg hb]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [charMult, sum_dihedral, hr, hsr, add_zero]
  field_simp

/-- Burnside's lemma for the vertex action: the trivial character occurs with multiplicity `1`
(the vertex action of the `n`-gon symmetry group is transitive). -/
theorem trivialChar_multiplicity (n : ℕ) [NeZero n] : charMult n (trivialChar n) = 1 := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hr : ∑ i : ZMod n, (permChar n (r i) : ℝ) * trivialChar n (r i) = (n : ℝ) := by
    rw [Finset.sum_eq_single (0 : ZMod n)]
    · rw [permChar_r, if_pos rfl, trivialChar, mul_one]
    · intro b _ hb; rw [permChar_r, if_neg hb]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsr : ∑ i : ZMod n, (permChar n (sr i) : ℝ) * trivialChar n (sr i) = (n : ℝ) := by
    have := sum_permChar_sr n
    simp only [trivialChar, mul_one]
    rw [← Nat.cast_sum, this]
  rw [charMult, sum_dihedral, hr, hsr]
  field_simp
  ring

/-- The sign character does not occur in the vertex representation of the regular `n`-gon. -/
theorem signChar_multiplicity (n : ℕ) [NeZero n] : charMult n (signChar n) = 0 := by
  classical
  have hr : ∑ i : ZMod n, (permChar n (r i) : ℝ) * signChar n (r i) = (n : ℝ) := by
    rw [Finset.sum_eq_single (0 : ZMod n)]
    · rw [permChar_r, if_pos rfl, signChar, mul_one]
    · intro b _ hb; rw [permChar_r, if_neg hb]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsr : ∑ i : ZMod n, (permChar n (sr i) : ℝ) * signChar n (sr i) = -(n : ℝ) := by
    have := sum_permChar_sr n
    simp only [signChar, mul_neg, mul_one, Finset.sum_neg_distrib]
    rw [← Nat.cast_sum, this]
  rw [charMult, sum_dihedral, hr, hsr]
  simp

/-- The pentagon case `n = 5`, `k = 1`: the first two-dimensional representation of `D₅`
occurs once in the vertex representation. -/
theorem pentagon_multiplicity_one : charMult 5 (dihedralChar 5 1) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5 1

/-- The pentagon case `n = 5`, `k = 2`: the second two-dimensional representation of `D₅`
occurs once in the vertex representation. -/
theorem pentagon_multiplicity_two : charMult 5 (dihedralChar 5 2) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5 2

/-- Dimension count for an odd `n`-gon: the trivial representation together with the
`(n-1)/2` two-dimensional representations `ρ_k`, `1 ≤ k ≤ (n-1)/2`, each occurring with
multiplicity one, account for all `n` dimensions of the vertex representation. -/
theorem odd_dimension_count (n : ℕ) [NeZero n] (hn : Odd n) :
    1 + ∑ _k ∈ Finset.Icc 1 ((n - 1) / 2), 2 = permChar n 1 := by
  rw [permChar_one]
  obtain ⟨m, rfl⟩ := hn
  simp
  omega

end Brockian

