import Mathlib

/-!
# Equivariance of the regular `n`-gon representation of the dihedral group

This file generalises the pentagon (`n = 5`, dihedral group `D₅`) picture to an arbitrary
regular `n`-gon.

The combinatorial model of the vertices of the `n`-gon is `ZMod n`, on which the dihedral group
`DihedralGroup n` acts by `r i • k = k + i` (rotation) and `sr i • k = -i - k` (reflection).

The geometric model is the set of `n`-th roots of unity in `ℂ`, on which `DihedralGroup n` acts by
`r i • z = ζ^i * z` and `sr i • z = ζ^(-i) * conj z`, where `ζ = exp (2πI / n)`.

The main result, `Brockian.PentagonPentagonEquivarianceGeneral`, says that the vertex map
`k ↦ exp (2πI k / n)` intertwines the two actions, for every `n > 0`.  The pentagon case is
recorded as `Brockian.pentagon_equivariance`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Complex

/-- The character `E n m = exp (2 π i m / n)`. -/
noncomputable def rootExp (n : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (n : ℂ))

lemma rootExp_add (n : ℕ) (a b : ℤ) :
    rootExp n (a + b) = rootExp n a * rootExp n b := by
  unfold rootExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma rootExp_zero (n : ℕ) : rootExp n 0 = 1 := by
  simp [rootExp]

lemma rootExp_natMul (n : ℕ) (hn : 0 < n) (t : ℤ) : rootExp n (n * t) = 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have : (2 * (Real.pi : ℂ) * Complex.I * ((n * t : ℤ) : ℂ) / (n : ℂ))
      = (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp
  rw [rootExp, this, Complex.exp_int_mul_two_pi_mul_I]

/-- `rootExp n` only depends on the residue class mod `n`. -/
lemma rootExp_congr (n : ℕ) (hn : 0 < n) {a b : ℤ} (h : (a : ZMod n) = (b : ZMod n)) :
    rootExp n a = rootExp n b := by
  have hdvd : (n : ℤ) ∣ a - b := by
    have : ((a - b : ℤ) : ZMod n) = 0 := by push_cast [h]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨t, ht⟩ := hdvd
  have : a = b + (n : ℤ) * t := by omega
  rw [this, rootExp_add, rootExp_natMul n hn, mul_one]

lemma conj_rootExp (n : ℕ) (m : ℤ) :
    (starRingEnd ℂ) (rootExp n m) = rootExp n (-m) := by
  unfold rootExp
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]

/-- The vertices of the regular `n`-gon, indexed by `ZMod n`. -/
noncomputable def ngonVertex (n : ℕ) (k : ZMod n) : ℂ := rootExp n (k.val : ℤ)

lemma ngonVertex_eq_rootExp (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ngonVertex n ((a : ZMod n)) = rootExp n a := by
  refine rootExp_congr n hn ?_
  haveI : NeZero n := ⟨hn.ne'⟩
  push_cast
  simp [ZMod.natCast_val]

/-- The combinatorial action of the dihedral group on the vertex labels `ZMod n`. -/
def vertexAct (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => k + i
  | DihedralGroup.sr i, k => -i - k

lemma vertexAct_one (n : ℕ) (k : ZMod n) : vertexAct n 1 k = k := by
  show vertexAct n (DihedralGroup.r 0) k = k
  simp [vertexAct]

/-- The combinatorial action is a genuine group action. -/
lemma vertexAct_mul (n : ℕ) (g h : DihedralGroup n) (k : ZMod n) :
    vertexAct n (g * h) k = vertexAct n g (vertexAct n h k) := by
  cases g with
  | r i => cases h with
    | r j => show k + (i + j) = (k + j) + i; ring
    | sr j => show -(j - i) - k = (-j - k) + i; ring
  | sr i => cases h with
    | r j => show -(i + j) - k = -i - (k + j); ring
    | sr j => show k + (j - i) = -i - (-j - k); ring

/-- The geometric action of the dihedral group on the complex plane:
rotations by `n`-th roots of unity and reflections. -/
noncomputable def planeAct (n : ℕ) : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => rootExp n (i.val : ℤ) * z
  | DihedralGroup.sr i, z => rootExp n (-(i.val : ℤ)) * (starRingEnd ℂ) z

lemma planeAct_one (n : ℕ) (z : ℂ) : planeAct n 1 z = z := by
  show planeAct n (DihedralGroup.r 0) z = z
  simp [planeAct, ZMod.val_zero, rootExp_zero]

/-- The plane action is a genuine group action. -/
lemma planeAct_mul (n : ℕ) (hn : 0 < n) (g h : DihedralGroup n) (z : ℂ) :
    planeAct n (g * h) z = planeAct n g (planeAct n h z) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a b : ℤ, rootExp n a * rootExp n b = rootExp n (a + b) := by
    intro a b; rw [rootExp_add]
  have cast_val : ∀ i : ZMod n, ((i.val : ℤ) : ZMod n) = i := by
    intro i; push_cast; simp [ZMod.natCast_val]
  cases g with
  | r i =>
    cases h with
    | r j =>
      show rootExp n (((i + j).val : ℤ)) * z = _
      have : rootExp n (((i + j : ZMod n).val : ℤ)) = rootExp n ((i.val : ℤ) + (j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct]
      ring
    | sr j =>
      show rootExp n (-(((j - i : ZMod n)).val : ℤ)) * (starRingEnd ℂ) z = _
      have : rootExp n (-(((j - i : ZMod n)).val : ℤ))
          = rootExp n ((i.val : ℤ) + -(j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct]
      ring
  | sr i =>
    cases h with
    | r j =>
      show rootExp n (-(((i + j : ZMod n)).val : ℤ)) * (starRingEnd ℂ) z = _
      have : rootExp n (-(((i + j : ZMod n)).val : ℤ))
          = rootExp n (-(i.val : ℤ) + -(j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct, conj_rootExp]
      ring
    | sr j =>
      show rootExp n (((j - i : ZMod n)).val : ℤ) * z = _
      have : rootExp n (((j - i : ZMod n)).val : ℤ)
          = rootExp n (-(i.val : ℤ) + (j.val : ℤ)) := by
        refine rootExp_congr n hn ?_
        push_cast [cast_val]
        ring
      rw [this, ← key]
      simp [planeAct, conj_rootExp]
      ring

/-- **Equivariance of the regular `n`-gon representation.**  For every `n > 0`, the vertex map
`ZMod n → ℂ`, `k ↦ exp (2 π i k / n)`, intertwines the combinatorial action of the dihedral
group `DihedralGroup n` on the vertex labels with its geometric action on the plane.  This
generalises the `D₅`/pentagon case to arbitrary `n`-gons. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) (hn : 0 < n)
    (g : DihedralGroup n) (k : ZMod n) :
    ngonVertex n (vertexAct n g k) = planeAct n g (ngonVertex n k) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have cast_val : ∀ i : ZMod n, ((i.val : ℤ) : ZMod n) = i := by
    intro i; push_cast; simp [ZMod.natCast_val]
  cases g with
  | r i =>
    show ngonVertex n (k + i) = rootExp n (i.val : ℤ) * ngonVertex n k
    have : ngonVertex n (k + i) = rootExp n ((k.val : ℤ) + (i.val : ℤ)) := by
      unfold ngonVertex
      refine rootExp_congr n hn ?_
      push_cast [cast_val]
      ring
    rw [this, rootExp_add]
    unfold ngonVertex
    ring
  | sr i =>
    show ngonVertex n (-i - k) = rootExp n (-(i.val : ℤ)) * (starRingEnd ℂ) (ngonVertex n k)
    have h1 : ngonVertex n (-i - k) = rootExp n (-(i.val : ℤ) + -(k.val : ℤ)) := by
      unfold ngonVertex
      refine rootExp_congr n hn ?_
      push_cast [cast_val]
      ring
    rw [h1, rootExp_add]
    unfold ngonVertex
    rw [conj_rootExp]

/-- The `n` vertices of the regular `n`-gon are pairwise distinct: the vertex map is injective. -/
theorem ngonVertex_injective (n : ℕ) (hn : 0 < n) : Function.Injective (ngonVertex n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  intro k l hkl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [ngonVertex, ngonVertex, rootExp, rootExp, Complex.exp_eq_exp_iff_exists_int] at hkl
  obtain ⟨t, ht⟩ := hkl
  have hval : ((k.val : ℤ) : ℂ) = ((l.val : ℤ) : ℂ) + (n : ℂ) * (t : ℂ) := by
    field_simp at ht
    push_cast
    linear_combination ht
  have hz : ((k.val : ℤ)) = ((l.val : ℤ)) + (n : ℤ) * t := by exact_mod_cast hval
  have : ((k.val : ℤ) : ZMod n) = ((l.val : ℤ) : ZMod n) := by
    rw [hz]; push_cast; simp
  simpa [ZMod.natCast_val] using this

/-- The pentagon (`n = 5`) case: the original `D₅` statement. -/
theorem pentagon_equivariance (g : DihedralGroup 5) (k : ZMod 5) :
    ngonVertex 5 (vertexAct 5 g k) = planeAct 5 g (ngonVertex 5 k) :=
  PentagonPentagonEquivarianceGeneral 5 (by norm_num) g k

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

