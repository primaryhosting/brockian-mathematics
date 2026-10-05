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

set_option grind.warning false

namespace Brockian

open DihedralGroup

/-! ## The action of the dihedral group on the vertices of the `n`-gon -/

/-- The action of `DihedralGroup n` on the `n` vertices of the regular `n`-gon,
whose vertices are labelled by `ZMod n`.  The rotation `r i` sends the vertex `x` to
`x - i` and the reflection `sr i` sends `x` to `i - x`. -/
def vertexPerm (n : ℕ) : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g := match g with
    | .r i => Equiv.subRight i
    | .sr i => Equiv.subLeft i
  map_one' := by
    ext x
    simp [DihedralGroup.one_def]
  map_mul' := by
    rintro (i | i) (j | j) <;> ext x <;>
      simp [Equiv.subRight, Equiv.subLeft, Equiv.Perm.mul_apply] <;> ring

@[simp] theorem vertexPerm_r (n : ℕ) (i x : ZMod n) : vertexPerm n (.r i) x = x - i := rfl

@[simp] theorem vertexPerm_sr (n : ℕ) (i x : ZMod n) : vertexPerm n (.sr i) x = i - x := rfl

/-! ## The permutation character of the vertex representation -/

/-- The permutation matrix (with complex entries) of the action of `g` on the vertices. -/
noncomputable def vertexMatrix (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun x y => if vertexPerm n g y = x then (1 : ℂ) else 0

/-- The character of the permutation representation of `DihedralGroup n` on the vertices of
the regular `n`-gon: the number of vertices fixed by `g`. -/
noncomputable def vertexChar (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℂ :=
  ∑ x : ZMod n, if vertexPerm n g x = x then (1 : ℂ) else 0

/-- The vertex character is indeed the trace of the permutation matrix. -/
theorem vertexChar_eq_trace (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    vertexChar n g = (vertexMatrix n g).trace := by
  simp [vertexChar, vertexMatrix, Matrix.trace, Matrix.diag]

/-- The vertex character counts the fixed vertices. -/
theorem vertexChar_eq_card_fixed (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    vertexChar n g = (Finset.univ.filter fun x : ZMod n => vertexPerm n g x = x).card := by
  simp [vertexChar, Finset.sum_ite, Finset.sum_const]

/-- A rotation fixes every vertex if it is trivial and no vertex otherwise. -/
theorem vertexChar_r (n : ℕ) [NeZero n] (i : ZMod n) :
    vertexChar n (.r i) = if i = 0 then (n : ℂ) else 0 := by
  have h : ∀ x : ZMod n, (vertexPerm n (.r i) x = x) ↔ i = 0 := by
    intro x
    simp [sub_eq_self]
  simp only [vertexChar, h]
  by_cases hi : i = 0 <;> simp [hi, ZMod.card]

/-- The value of the vertex character at the identity is the number of vertices. -/
theorem vertexChar_one (n : ℕ) [NeZero n] : vertexChar n 1 = (n : ℂ) := by
  rw [DihedralGroup.one_def, vertexChar_r]
  simp

/-- Summing the number of vertices fixed by the reflections gives `n`
(each vertex `x` is fixed by exactly one reflection, namely `sr (2x)`). -/
theorem sum_vertexChar_sr (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, vertexChar n (.sr i) = (n : ℂ) := by
  have h : ∀ i x : ZMod n, (vertexPerm n (.sr i) x = x) ↔ i = x + x := by
    intro i x
    constructor
    · intro hx
      have : i - x = x := hx
      linear_combination this
    · intro hx
      show i - x = x
      rw [hx]; ring
  simp only [vertexChar, h]
  rw [Finset.sum_comm]
  have : ∀ x : ZMod n, (∑ i : ZMod n, if i = x + x then (1 : ℂ) else 0) = 1 := by
    intro x
    simp
  simp [this, ZMod.card]

/-! ## The two-dimensional characters of the dihedral group -/

/-- A primitive `n`-th root of unity in `ℂ`. -/
noncomputable def dihedralZeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The character of the two-dimensional representation `ρ_h` of `DihedralGroup n`:
it takes the value `ζ^(h i) + ζ^(-h i)` on the rotation `r i` and `0` on every reflection. -/
noncomputable def twoDimChar (n h : ℕ) : DihedralGroup n → ℂ
  | .r i => dihedralZeta n ^ (h * i.val) + (dihedralZeta n)⁻¹ ^ (h * i.val)
  | .sr _ => 0

@[simp] theorem twoDimChar_sr (n h : ℕ) (i : ZMod n) : twoDimChar n h (.sr i) = 0 := rfl

@[simp] theorem twoDimChar_one (n h : ℕ) [NeZero n] : twoDimChar n h 1 = 2 := by
  have h0 : ((0 : ZMod n)).val = 0 := ZMod.val_zero n
  simp [DihedralGroup.one_def, twoDimChar, h0]

/-! ## Multiplicities -/

/-- Splitting a sum over the dihedral group into rotations and reflections. -/
theorem sum_dihedral {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n]
    (f : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, f g = (∑ i : ZMod n, f (.r i)) + ∑ i : ZMod n, f (.sr i) := by
  let e : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n :=
    { toFun := fun x => match x with | .inl j => .r j | .inr j => .sr j
      invFun := fun g => match g with | .r j => .inl j | .sr j => .inr j
      left_inv := by rintro (j | j) <;> rfl
      right_inv := by rintro (j | j) <;> rfl }
  rw [← Fintype.sum_equiv e (fun x => f (e x)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-- The multiplicity `⟨χ_vertex, χ⟩` of the character `χ` in the vertex representation
of the regular `n`-gon. -/
noncomputable def charMultiplicity (n : ℕ) [NeZero n] (χ : DihedralGroup n → ℂ) : ℂ :=
  (1 / (2 * n)) * ∑ g : DihedralGroup n, vertexChar n g * (starRingEnd ℂ) (χ g)

/-- **Pentagon Pentagon Character Multiplicity Ext.**
For every regular `n`-gon (`n ≥ 1`), the permutation representation on the vertices contains
each two-dimensional character `χ_h` of the dihedral symmetry group with multiplicity exactly `1`,
and the trivial character with multiplicity exactly `1`.  For `n = 5` this is the classical
statement for the pentagon and the dihedral group `D₅`. -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] (h : ℕ) :
    charMultiplicity n (twoDimChar n h) = 1 ∧ charMultiplicity n (fun _ => 1) = 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  constructor
  · rw [charMultiplicity, sum_dihedral]
    have hsr : ∀ i : ZMod n,
        vertexChar n (.sr i) * (starRingEnd ℂ) (twoDimChar n h (.sr i)) = 0 := by
      intro i; simp
    have hr : ∀ i : ZMod n,
        vertexChar n (.r i) * (starRingEnd ℂ) (twoDimChar n h (.r i))
          = if i = 0 then (2 * n : ℂ) else 0 := by
      intro i
      rw [vertexChar_r]
      by_cases hi : i = 0
      · subst hi
        have : twoDimChar n h (.r (0 : ZMod n)) = 2 := by
          simpa [DihedralGroup.one_def] using twoDimChar_one n h
        simp [this]
        ring
      · simp [hi]
    simp only [hr, hsr, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq' Finset.univ
      (0 : ZMod n) (fun _ => (2 * n : ℂ)), Finset.mem_univ, if_true]
    field_simp
  · rw [charMultiplicity, sum_dihedral]
    simp only [map_one, mul_one]
    rw [sum_vertexChar_sr]
    have hrsum : ∑ i : ZMod n, vertexChar n (.r i) = (n : ℂ) := by
      simp only [vertexChar_r]
      rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod n) (fun _ => (n : ℂ))]
      simp
    rw [hrsum]
    field_simp
    ring

/-! ## The pentagon -/

/-- For the pentagon (`n = 5`) each of the two two-dimensional characters of `D₅` occurs
exactly once in the vertex representation. -/
theorem pentagon_twoDimChar_multiplicity (h : ℕ) :
    charMultiplicity 5 (twoDimChar 5 h) = 1 :=
  (PentagonPentagonCharacterMultiplicityExt 5 h).1

/-- For the pentagon the trivial character occurs exactly once in the vertex representation. -/
theorem pentagon_trivial_multiplicity :
    charMultiplicity 5 (fun _ => 1) = 1 :=
  (PentagonPentagonCharacterMultiplicityExt 5 1).2

end Brockian

