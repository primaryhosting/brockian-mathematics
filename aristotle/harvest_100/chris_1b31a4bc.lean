import RequestProject.PentagonExt

/-!
# Decomposition of the vertex representation of a regular `n`-gon, `n` odd

For an odd number of vertices `n = 2m+1`, the permutation character of `DihedralGroup n`
acting on the vertices of the regular `n`-gon decomposes as the trivial character plus the
`m` two-dimensional characters `rotChar n 1, …, rotChar n m`.

For `n = 5` this is the classical pentagon statement `5 = 1 + 2 + 2`.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- For an odd `n`-gon every reflection fixes exactly one vertex. -/
lemma permChar_sr_odd [NeZero n] (hodd : Odd n) (i : ZMod n) : permChar n (sr i) = 1 := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hc : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hodd
    simpa using (ZMod.isUnit_iff_coprime 2 n).mpr hc
  obtain ⟨u, hu⟩ := h2
  have key : fixedVertices n (sr i) = {(↑u⁻¹ * i : ZMod n)} := by
    ext x
    simp only [fixedVertices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      ngonAct_sr]
    constructor
    · intro h
      have hx : (u : ZMod n) * x = i := by rw [hu]; linear_combination -h
      rw [← hx, ← mul_assoc]
      simp
    · rintro rfl
      have hx : (u : ZMod n) * (↑u⁻¹ * i) = i := by rw [← mul_assoc]; simp
      rw [hu] at hx
      linear_combination -hx
  rw [permChar, key, Finset.card_singleton, Nat.cast_one]

/-- The value of the two-dimensional character on a rotation, expressed with roots of unity. -/
lemma rotChar_r_eq_rootPow [NeZero n] (i : ZMod n) (j : ℕ) (hj : j ≤ n) :
    ((rotChar n j (r i) : ℝ) : ℂ) =
      (ZMod.stdAddChar i) ^ j + (ZMod.stdAddChar i) ^ (n - j) := by
  have hpow : (ZMod.stdAddChar i : ℂ) ^ j = rootPow n j i := by
    rw [← AddChar.map_nsmul_eq_pow, rootPow]
    congr 1
    simp [nsmul_eq_mul]
  have hn : (ZMod.stdAddChar i : ℂ) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show (n : ℕ) • i = 0 by simp [nsmul_eq_mul],
      AddChar.map_zero_eq_one]
  have hsplit : (ZMod.stdAddChar i : ℂ) ^ (n - j) * (ZMod.stdAddChar i : ℂ) ^ j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, hn]
  have hinv : (ZMod.stdAddChar i : ℂ) ^ (n - j) = (rootPow n j i)⁻¹ := by
    rw [← hpow]
    exact eq_inv_of_mul_eq_one_left hsplit
  have htrace := rotChar_eq_trace n j (r i)
  rw [htrace]
  show Matrix.trace !![rootPow n j i, 0; 0, rootPow n j (-i)] = _
  rw [Matrix.trace_fin_two_of, hpow, hinv]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact rootPow_mul_neg n j i)

/-- The full sum of the powers of the root of unity attached to `i : ZMod n`. -/
lemma sum_pow_stdAddChar [NeZero n] (i : ZMod n) :
    ∑ k ∈ Finset.range n, (ZMod.stdAddChar i) ^ k = if i = 0 then (n : ℂ) else 0 := by
  by_cases h : i = 0
  · subst h; simp
  · rw [if_neg h]
    have hne : (ZMod.stdAddChar i : ℂ) ≠ 1 := fun hc =>
      h (ZMod.injective_stdAddChar (by rw [hc]; simp))
    have hpow : (ZMod.stdAddChar i : ℂ) ^ n = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, show (n : ℕ) • i = 0 by simp [nsmul_eq_mul],
        AddChar.map_zero_eq_one]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- Splitting a sum over `range (2m+1)` into the zero term and the pairs `{j, n - j}`. -/
lemma sum_range_odd_split (m : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ Finset.range (2 * m + 1), F k
      = F 0 + ∑ j ∈ Finset.Icc 1 m, (F j + F (2 * m + 1 - j)) := by
  have hsplit : ∑ k ∈ Finset.range (2 * m + 1), F k
      = (∑ k ∈ Finset.Ico 0 (m + 1), F k) + ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), F k := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive] <;> omega
  have h1 : ∑ k ∈ Finset.Ico 0 (m + 1), F k = F 0 + ∑ j ∈ Finset.Icc 1 m, F j := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    congr 1
  have h2 : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), F k
      = ∑ j ∈ Finset.Icc 1 m, F (2 * m + 1 - j) := by
    apply Finset.sum_nbij' (i := fun k => 2 * m + 1 - k) (j := fun k => 2 * m + 1 - k) <;>
      intro a ha <;> simp only [Finset.mem_Ico, Finset.mem_Icc] at * <;> try omega
    congr 1
    omega
  rw [hsplit, h1, h2, Finset.sum_add_distrib]
  ring

/-- **Decomposition of the vertex representation of an odd `n`-gon.**
For `n = 2m+1`, the permutation character of the action of `DihedralGroup n` on the vertices
is the sum of the trivial character and the `m` two-dimensional characters
`rotChar n 1, …, rotChar n m`. In particular the vertex representation has dimension
`n = 1 + 2m`. -/
theorem permChar_odd_decomposition (m : ℕ) (g : DihedralGroup (2 * m + 1)) :
    permChar (2 * m + 1) g
      = trivChar (2 * m + 1) g + ∑ j ∈ Finset.Icc 1 m, rotChar (2 * m + 1) j g := by
  have hodd : Odd (2 * m + 1) := ⟨m, by omega⟩
  cases g with
  | sr i =>
    rw [permChar_sr_odd hodd i]
    simp [trivChar, rotChar]
  | r i =>
    have hsum : ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ)
        = ∑ j ∈ Finset.Icc 1 m,
            ((ZMod.stdAddChar i) ^ j + (ZMod.stdAddChar i) ^ (2 * m + 1 - j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      exact rotChar_r_eq_rootPow i j (by omega)
    have hLHS : ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
        = if i = 0 then ((2 * m + 1 : ℕ) : ℂ) else 0 := by
      by_cases h : i = 0
      · subst h; rw [permChar_r_zero, if_pos rfl]; push_cast; ring
      · rw [permChar_r_of_ne_zero h, if_neg h, Complex.ofReal_zero]
    have hgoal : ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
        = ((trivChar (2 * m + 1) (r i) : ℝ) : ℂ)
          + ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ) := by
      calc ((permChar (2 * m + 1) (r i) : ℝ) : ℂ)
          = if i = 0 then ((2 * m + 1 : ℕ) : ℂ) else 0 := hLHS
        _ = ∑ k ∈ Finset.range (2 * m + 1), (ZMod.stdAddChar i : ℂ) ^ k :=
            (sum_pow_stdAddChar i).symm
        _ = (ZMod.stdAddChar i : ℂ) ^ 0
              + ∑ j ∈ Finset.Icc 1 m,
                  ((ZMod.stdAddChar i : ℂ) ^ j + (ZMod.stdAddChar i : ℂ) ^ (2 * m + 1 - j)) :=
            sum_range_odd_split m _
        _ = ((trivChar (2 * m + 1) (r i) : ℝ) : ℂ)
              + ∑ j ∈ Finset.Icc 1 m, ((rotChar (2 * m + 1) j (r i) : ℝ) : ℂ) := by
            rw [hsum]
            simp [trivChar]
    exact_mod_cast hgoal

/-- The pentagon: the permutation representation on the five vertices is the sum of the
trivial representation and the two two-dimensional representations, `5 = 1 + 2 + 2`. -/
theorem pentagon_decomposition (g : DihedralGroup 5) :
    permChar 5 g = trivChar 5 g + rotChar 5 1 g + rotChar 5 2 g := by
  have h := permChar_odd_decomposition 2 g
  simpa [Finset.sum_Icc_succ_top, add_assoc] using h

end Brockian

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

import Mathlib

/-!
# Character multiplicities of the vertex representation of a regular `n`-gon

The regular pentagon has symmetry group `DihedralGroup 5`, acting on its five vertices.
Here we generalize the pentagon computations to an arbitrary regular `n`-gon
(`n ≥ 1`, i.e. `[NeZero n]`), whose symmetry group is `DihedralGroup n` acting on the
vertex set `ZMod n`.

The main result, `Brockian.PentagonPentagonCharacterMultiplicityExt`, computes the
multiplicity of the trivial character, of the sign character, and of each two-dimensional
rotation character inside the permutation character of the vertex action:
they are `1`, `0` and `1` respectively.
-/

open Finset

namespace Brockian

open DihedralGroup

variable {n : ℕ}

/-- The action of a dihedral symmetry on the vertex set `ZMod n` of the regular `n`-gon.
The rotation `r i` acts by `x ↦ x - i` and the reflection `sr i` acts by `x ↦ i - x`;
these conventions make the map `g ↦ (x ↦ ngonAct n g x)` a genuine group action. -/
def ngonAct (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, x => x - i
  | DihedralGroup.sr i, x => i - x

@[simp] lemma ngonAct_r (i x : ZMod n) : ngonAct n (r i) x = x - i := rfl
@[simp] lemma ngonAct_sr (i x : ZMod n) : ngonAct n (sr i) x = i - x := rfl

lemma ngonAct_one (x : ZMod n) : ngonAct n 1 x = x := sub_zero x

lemma ngonAct_mul (g h : DihedralGroup n) (x : ZMod n) :
    ngonAct n (g * h) x = ngonAct n g (ngonAct n h x) := by
  cases g <;> cases h <;> simp <;> ring

lemma ngonAct_left_inverse (g : DihedralGroup n) (x : ZMod n) :
    ngonAct n g⁻¹ (ngonAct n g x) = x := by
  rw [← ngonAct_mul, inv_mul_cancel, ngonAct_one]

/-- The vertex action of the dihedral group, as a homomorphism into the permutations
of the vertex set. -/
def ngonPerm (n : ℕ) : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g :=
    { toFun := ngonAct n g
      invFun := ngonAct n g⁻¹
      left_inv := ngonAct_left_inverse g
      right_inv := by
        intro x
        have := ngonAct_left_inverse g⁻¹ x
        rwa [inv_inv] at this }
  map_one' := by ext x; exact ngonAct_one x
  map_mul' g h := by ext x; exact ngonAct_mul g h x

@[simp] lemma ngonPerm_apply (g : DihedralGroup n) (x : ZMod n) :
    ngonPerm n g x = ngonAct n g x := rfl

/-- The set of vertices of the `n`-gon fixed by a dihedral symmetry. -/
noncomputable def fixedVertices (n : ℕ) [NeZero n] (g : DihedralGroup n) : Finset (ZMod n) :=
  Finset.univ.filter fun x => ngonAct n g x = x

/-- The permutation character of the vertex representation: the number of fixed vertices. -/
noncomputable def permChar (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℝ :=
  ((fixedVertices n g).card : ℝ)

/-- The trivial character of the dihedral group. -/
def trivChar (n : ℕ) : DihedralGroup n → ℝ := fun _ => 1

/-- The sign character of the dihedral group: `1` on rotations, `-1` on reflections. -/
def signChar (n : ℕ) : DihedralGroup n → ℝ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => -1

/-- The character of the two-dimensional rotation representation with parameter `j`:
it takes the value `2 cos (2π j i / n)` on the rotation `r i` and `0` on every reflection. -/
noncomputable def rotChar (n : ℕ) (j : ℕ) : DihedralGroup n → ℝ
  | DihedralGroup.r i => 2 * Real.cos (2 * Real.pi * j * i.val / n)
  | DihedralGroup.sr _ => 0

/-- The inner product of two (real valued) class functions on `DihedralGroup n`. -/
noncomputable def charInner (n : ℕ) [NeZero n] (f g : DihedralGroup n → ℝ) : ℝ :=
  (1 / (Fintype.card (DihedralGroup n) : ℝ)) * ∑ x : DihedralGroup n, f x * g x

/-- Splitting a sum over the dihedral group into rotations and reflections. -/
lemma sum_dihedral [NeZero n] (f : DihedralGroup n → ℝ) :
    ∑ g : DihedralGroup n, f g = (∑ i : ZMod n, f (r i)) + ∑ i : ZMod n, f (sr i) := by
  classical
  let e : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n :=
    { toFun := Sum.elim DihedralGroup.r DihedralGroup.sr
      invFun := fun g => match g with
        | DihedralGroup.r i => Sum.inl i
        | DihedralGroup.sr i => Sum.inr i
      left_inv := by rintro (x | x) <;> rfl
      right_inv := by rintro (x | x) <;> rfl }
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  rfl

lemma permChar_r_zero [NeZero n] : permChar n (r 0) = (n : ℝ) := by
  have h : fixedVertices n (r (0 : ZMod n)) = Finset.univ :=
    Finset.filter_true_of_mem (fun x _ => sub_zero x)
  rw [permChar, h, Finset.card_univ, ZMod.card]

lemma permChar_r_of_ne_zero [NeZero n] {i : ZMod n} (hi : i ≠ 0) : permChar n (r i) = 0 := by
  have : fixedVertices n (r i) = ∅ := by
    ext x
    simp only [fixedVertices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, ngonAct_r]
    intro h
    exact hi (by linear_combination -h)
  simp [permChar, this]

lemma sum_permChar_r [NeZero n] : ∑ i : ZMod n, permChar n (r i) = (n : ℝ) := by
  rw [Finset.sum_eq_single (0 : ZMod n)]
  · exact permChar_r_zero
  · intro b _ hb; exact permChar_r_of_ne_zero hb
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_permChar_sr [NeZero n] : ∑ i : ZMod n, permChar n (sr i) = (n : ℝ) := by
  classical
  have key : ∑ i : ZMod n, (fixedVertices n (sr i)).card = Fintype.card (ZMod n) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun x : ZMod n => x + x) (s := (Finset.univ : Finset (ZMod n)))
      (t := (Finset.univ : Finset (ZMod n))) (fun x _ => Finset.mem_univ _)
    have hfe : ∀ i : ZMod n,
        (Finset.univ.filter fun x : ZMod n => x + x = i) = fixedVertices n (sr i) := by
      intro i
      ext x
      simp only [fixedVertices, Finset.mem_filter, Finset.mem_univ, true_and, ngonAct_sr]
      constructor
      · intro h; linear_combination -h
      · intro h; linear_combination -h
    simp only [hfe] at hfib
    rw [← hfib, Finset.card_univ]
  calc ∑ i : ZMod n, permChar n (sr i)
      = ((∑ i : ZMod n, (fixedVertices n (sr i)).card : ℕ) : ℝ) := by
        push_cast [permChar]; ring
    _ = (n : ℝ) := by rw [key, ZMod.card]

/-- **Main result.** For every regular `n`-gon (`n ≥ 1`), the permutation character of the
action of `DihedralGroup n` on the vertices contains the trivial character with multiplicity
`1`, the sign character with multiplicity `0`, and every two-dimensional rotation character
with multiplicity `1`. Taking `n = 5` recovers the pentagon case.

(For the parameters `j` for which `rotChar n j` is the character of a reducible
two-dimensional representation, such as `j = 0`, the stated number is the inner product
`⟨permChar, rotChar n j⟩`, which is still `1`.) -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    charInner n (permChar n) (trivChar n) = 1 ∧
    charInner n (permChar n) (signChar n) = 0 ∧
    ∀ j : ℕ, charInner n (permChar n) (rotChar n j) = 1 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcard : (Fintype.card (DihedralGroup n) : ℝ) = 2 * n := by
    rw [DihedralGroup.card]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [charInner, hcard, sum_dihedral]
    simp only [trivChar, mul_one]
    rw [sum_permChar_r, sum_permChar_sr]
    field_simp
    ring
  · rw [charInner, hcard, sum_dihedral]
    simp only [signChar, mul_one, mul_neg]
    rw [Finset.sum_neg_distrib, sum_permChar_r, sum_permChar_sr]
    ring
  · intro j
    rw [charInner, hcard, sum_dihedral]
    have h2 : ∑ i : ZMod n, permChar n (sr i) * rotChar n j (sr i) = 0 := by
      simp [rotChar]
    have h1 : ∑ i : ZMod n, permChar n (r i) * rotChar n j (r i) = 2 * n := by
      rw [Finset.sum_eq_single (0 : ZMod n)]
      · rw [permChar_r_zero]
        simp [rotChar]
        ring
      · intro b _ hb; rw [permChar_r_of_ne_zero hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2, add_zero]
    field_simp

/-!
### The characters above really are characters of representations
-/

/-- The trivial character is the character of the trivial one-dimensional representation. -/
def trivCharHom (n : ℕ) : DihedralGroup n →* ℝ where
  toFun := trivChar n
  map_one' := rfl
  map_mul' _ _ := (one_mul 1).symm

/-- The sign character is a group homomorphism, i.e. the character of the one-dimensional
representation sending rotations to `1` and reflections to `-1`. -/
def signCharHom (n : ℕ) : DihedralGroup n →* ℝ where
  toFun := signChar n
  map_one' := rfl
  map_mul' g h := by
    cases g <;> cases h <;> simp [signChar]

@[simp] lemma signCharHom_apply (g : DihedralGroup n) : signCharHom n g = signChar n g := rfl

/-- The `n`-th root of unity `exp (2π I j k / n)`, as a function of `k : ZMod n`. -/
noncomputable def rootPow (n : ℕ) [NeZero n] (j : ℕ) (k : ZMod n) : ℂ :=
  ZMod.stdAddChar ((j : ZMod n) * k)

lemma rootPow_zero (n : ℕ) [NeZero n] (j : ℕ) : rootPow n j 0 = 1 := by
  simp [rootPow]

lemma rootPow_add (n : ℕ) [NeZero n] (j : ℕ) (a b : ZMod n) :
    rootPow n j (a + b) = rootPow n j a * rootPow n j b := by
  simp [rootPow, mul_add, AddChar.map_add_eq_mul]

lemma rootPow_mul_neg (n : ℕ) [NeZero n] (j : ℕ) (a : ZMod n) :
    rootPow n j a * rootPow n j (-a) = 1 := by
  rw [← rootPow_add, add_neg_cancel, rootPow_zero]

lemma rootPow_eq_exp (n : ℕ) [NeZero n] (j : ℕ) (k : ZMod n) :
    rootPow n j k = Complex.exp (2 * Real.pi * Complex.I * (j * k.val) / n) := by
  have h : ((j : ZMod n) * k) = ((j * k.val : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_val, ZMod.ringHom_map_cast]
    simp
  rw [rootPow, h, show ((j * k.val : ℕ) : ZMod n) = ((j * k.val : ℤ) : ZMod n) by push_cast; ring,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- The two-dimensional complex representation of `DihedralGroup n` with parameter `j`:
the rotation `r i` acts diagonally by the root of unity `exp (2π I j i / n)` and its inverse,
and the reflections swap the two eigenlines. -/
noncomputable def twoDimRep (n : ℕ) [NeZero n] (j : ℕ) :
    DihedralGroup n →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun g := match g with
    | DihedralGroup.r i => !![rootPow n j i, 0; 0, rootPow n j (-i)]
    | DihedralGroup.sr i => !![0, rootPow n j (-i); rootPow n j i, 0]
  map_one' := by
    show !![rootPow n j 0, 0; 0, rootPow n j (-0)] = 1
    rw [Matrix.one_fin_two, neg_zero, rootPow_zero]
  map_mul' g h := by
    cases g with
    | r a =>
      cases h with
      | r b =>
        show !![rootPow n j (a + b), 0; 0, rootPow n j (-(a + b))] = _ * _
        rw [Matrix.mul_fin_two, rootPow_add, show -(a + b) = (-a) + (-b) by ring, rootPow_add]
        norm_num
      | sr b =>
        show !![0, rootPow n j (-(b - a)); rootPow n j (b - a), 0] = _ * _
        rw [Matrix.mul_fin_two, show b - a = b + (-a) by ring, rootPow_add,
          show -(b + -a) = (-b) + a by ring, rootPow_add]
        norm_num
        constructor <;> ring
    | sr a =>
      cases h with
      | r b =>
        show !![0, rootPow n j (-(a + b)); rootPow n j (a + b), 0] = _ * _
        rw [Matrix.mul_fin_two, rootPow_add, show -(a + b) = (-a) + (-b) by ring, rootPow_add]
        norm_num
      | sr b =>
        show !![rootPow n j (b - a), 0; 0, rootPow n j (-(b - a))] = _ * _
        rw [Matrix.mul_fin_two, show b - a = b + (-a) by ring, rootPow_add,
          show -(b + -a) = (-b) + a by ring, rootPow_add]
        norm_num
        constructor <;> ring

/-- `rotChar n j` is the character (trace) of the two-dimensional representation
`twoDimRep n j`. -/
lemma rotChar_eq_trace (n : ℕ) [NeZero n] (j : ℕ) (g : DihedralGroup n) :
    ((rotChar n j g : ℝ) : ℂ) = Matrix.trace (twoDimRep n j g) := by
  cases g with
  | r i =>
    show ((2 * Real.cos (2 * Real.pi * j * i.val / n) : ℝ) : ℂ) =
      Matrix.trace !![rootPow n j i, 0; 0, rootPow n j (-i)]
    rw [Matrix.trace_fin_two_of]
    have hi : rootPow n j (-i) = (rootPow n j i)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact rootPow_mul_neg n j i)
    rw [rootPow_eq_exp, hi, rootPow_eq_exp, ← Complex.exp_neg]
    push_cast
    rw [Complex.cos]
    ring_nf
  | sr i =>
    show ((0 : ℝ) : ℂ) = Matrix.trace !![0, rootPow n j (-i); rootPow n j i, 0]
    rw [Matrix.trace_fin_two_of]
    norm_num

/-!
### The pentagon case
-/

/-- The pentagon (`n = 5`) case of the main theorem: in the permutation representation on the
five vertices, the trivial character occurs with multiplicity `1`, the sign character with
multiplicity `0`, and each two-dimensional character with multiplicity `1`. -/
theorem pentagon_character_multiplicity :
    charInner 5 (permChar 5) (trivChar 5) = 1 ∧
    charInner 5 (permChar 5) (signChar 5) = 0 ∧
    ∀ j : ℕ, charInner 5 (permChar 5) (rotChar 5 j) = 1 :=
  PentagonPentagonCharacterMultiplicityExt 5

end Brockian

