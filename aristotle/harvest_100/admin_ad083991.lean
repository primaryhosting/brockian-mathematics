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

set_option grind.warning false

/-!
# The dihedral symmetries of a regular `n`-gon, and their equivariance

This file generalizes the `D₅` (pentagon) representation results to arbitrary regular `n`-gons.

The vertices of the regular `n`-gon are the `n`-th roots of unity
`ngonVertex n k = exp (2 π i k / n)`, indexed by `k : ZMod n`.

`DihedralGroup n` acts
* combinatorially on the index set `ZMod n` (`Brockian.vertexAction`), and
* geometrically on the complex plane by rotations and reflections (`Brockian.planeMap`).

The main theorem `Brockian.PentagonPentagonEquivarianceGeneral` states that the vertex map
`ZMod n → ℂ` intertwines these two actions, for every `n ≠ 0`.  The pentagon case `n = 5`
is recovered as `Brockian.pentagon_equivariance`.
-/

namespace Brockian

open Complex

/-! ### Vertices of the regular `n`-gon -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle:
`exp (2 π i k / n)`. -/
noncomputable def ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (n : ℂ))

variable {n : ℕ} [NeZero n]

lemma ngonVertex_eq_toCircle (k : ZMod n) :
    ngonVertex n k = (ZMod.toCircle k : ℂ) := by
  rw [ngonVertex, ZMod.toCircle_apply]

@[simp] lemma ngonVertex_zero : ngonVertex n 0 = 1 := by
  simp [ngonVertex_eq_toCircle]

@[simp] lemma ngonVertex_add (k j : ZMod n) :
    ngonVertex n (k + j) = ngonVertex n k * ngonVertex n j := by
  simp [ngonVertex_eq_toCircle, AddChar.map_add_eq_mul]

@[simp] lemma norm_ngonVertex (k : ZMod n) : ‖ngonVertex n k‖ = 1 := by
  rw [ngonVertex_eq_toCircle]
  exact Circle.norm_coe _

@[simp] lemma ngonVertex_neg (k : ZMod n) :
    ngonVertex n (-k) = (starRingEnd ℂ) (ngonVertex n k) := by
  rw [← Complex.inv_eq_conj (norm_ngonVertex k)]
  have h : ngonVertex n (-k) * ngonVertex n k = 1 := by
    rw [← ngonVertex_add]; simp
  exact eq_inv_of_mul_eq_one_left h

lemma ngonVertex_sub (k j : ZMod n) :
    ngonVertex n (k - j) = ngonVertex n k * (starRingEnd ℂ) (ngonVertex n j) := by
  rw [sub_eq_add_neg, ngonVertex_add, ngonVertex_neg]

lemma ngonVertex_ne_zero (k : ZMod n) : ngonVertex n k ≠ 0 := by
  intro h
  have := norm_ngonVertex k
  rw [h] at this
  simp at this

/-- The vertex map is injective: the regular `n`-gon really has `n` distinct vertices. -/
lemma ngonVertex_injective : Function.Injective (ngonVertex n) := by
  intro a b hab
  refine ZMod.injective_toCircle (N := n) ?_
  ext
  rw [← ngonVertex_eq_toCircle, ← ngonVertex_eq_toCircle, hab]

/-! ### The combinatorial action of `DihedralGroup n` on the vertex labels -/

/-- The action of the dihedral group on the vertex labels `ZMod n`: the rotation `r i` sends the
label `k` to `i + k`, and the reflection `sr i` sends `k` to `-i - k`. -/
def vertexAction : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => i + k
  | DihedralGroup.sr i, k => -i - k

omit [NeZero n] in
@[simp] lemma vertexAction_r (i k : ZMod n) :
    vertexAction (DihedralGroup.r i) k = i + k := rfl

omit [NeZero n] in
@[simp] lemma vertexAction_sr (i k : ZMod n) :
    vertexAction (DihedralGroup.sr i) k = -i - k := rfl

omit [NeZero n] in
lemma vertexAction_one (k : ZMod n) : vertexAction (1 : DihedralGroup n) k = k := by
  show vertexAction (DihedralGroup.r 0) k = k
  exact zero_add k

omit [NeZero n] in
lemma vertexAction_mul (g h : DihedralGroup n) (k : ZMod n) :
    vertexAction (g * h) k = vertexAction g (vertexAction h k) := by
  cases g <;> cases h <;> simp <;> ring

/-- The dihedral group acts on the labels of the vertices of the regular `n`-gon. -/
instance : MulAction (DihedralGroup n) (ZMod n) where
  smul := vertexAction
  one_smul := vertexAction_one
  mul_smul := vertexAction_mul

omit [NeZero n] in
lemma smul_eq_vertexAction (g : DihedralGroup n) (k : ZMod n) :
    g • k = vertexAction g k := rfl

/-! ### The geometric action of `DihedralGroup n` on the plane -/

/-- The geometric realization of a dihedral symmetry as a map of the complex plane:
the rotation `r i` acts as multiplication by `exp (2 π i i / n)`, and the reflection `sr i`
acts as complex conjugation followed by multiplication by `exp (-2 π i i / n)`. -/
noncomputable def planeMap : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => ngonVertex n i * z
  | DihedralGroup.sr i, z => ngonVertex n (-i) * (starRingEnd ℂ) z

@[simp] lemma planeMap_r (i : ZMod n) (z : ℂ) :
    planeMap (DihedralGroup.r i) z = ngonVertex n i * z := rfl

@[simp] lemma planeMap_sr (i : ZMod n) (z : ℂ) :
    planeMap (DihedralGroup.sr i) z = ngonVertex n (-i) * (starRingEnd ℂ) z := rfl

lemma planeMap_one (z : ℂ) : planeMap (1 : DihedralGroup n) z = z := by
  show planeMap (DihedralGroup.r 0) z = z
  rw [planeMap_r, ngonVertex_zero, one_mul]

lemma planeMap_mul (g h : DihedralGroup n) (z : ℂ) :
    planeMap (g * h) z = planeMap g (planeMap h z) := by
  cases g with
  | r i =>
      cases h with
      | r j =>
          simp only [DihedralGroup.r_mul_r, planeMap_r]
          rw [ngonVertex_add, mul_assoc]
      | sr j =>
          simp only [DihedralGroup.r_mul_sr, planeMap_sr, planeMap_r]
          rw [← mul_assoc, ← ngonVertex_add]
          ring_nf
  | sr i =>
      cases h with
      | r j =>
          simp only [DihedralGroup.sr_mul_r, planeMap_sr, planeMap_r, map_mul]
          rw [← mul_assoc, ← ngonVertex_neg, ← ngonVertex_add]
          ring_nf
      | sr j =>
          simp only [DihedralGroup.sr_mul_sr, planeMap_sr, planeMap_r, map_mul,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
          rw [← ngonVertex_neg, neg_neg, ← mul_assoc, ← ngonVertex_add]
          ring_nf

/-- The geometric action of the dihedral group on the plane. -/
noncomputable instance : MulAction (DihedralGroup n) ℂ where
  smul := planeMap
  one_smul := planeMap_one
  mul_smul := planeMap_mul

lemma smul_eq_planeMap (g : DihedralGroup n) (z : ℂ) :
    g • z = planeMap g z := rfl

/-- Every dihedral symmetry acts on the plane by an isometry. -/
lemma dist_planeMap (g : DihedralGroup n) (z w : ℂ) :
    dist (planeMap g z) (planeMap g w) = dist z w := by
  cases g with
  | r i =>
      simp only [planeMap_r, Complex.dist_eq, ← mul_sub, norm_mul, norm_ngonVertex, one_mul]
  | sr i =>
      simp only [planeMap_sr, Complex.dist_eq, ← mul_sub, ← map_sub, norm_mul,
        norm_ngonVertex, one_mul, RCLike.norm_conj]

/-! ### Equivariance -/

/-- **Equivariance of the vertex map of the regular `n`-gon.**

For every `n ≠ 0`, every dihedral symmetry `g ∈ DihedralGroup n` and every vertex label
`k : ZMod n`, the geometric symmetry `planeMap g` carries the `k`-th vertex of the regular
`n`-gon to the `(g • k)`-th vertex.  This is the generalization to arbitrary `n` of the
pentagon (`D₅`) equivariance statement. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n]
    (g : DihedralGroup n) (k : ZMod n) :
    planeMap g (ngonVertex n k) = ngonVertex n (vertexAction g k) := by
  cases g with
  | r i => rw [planeMap_r, vertexAction_r, ngonVertex_add]
  | sr i =>
      rw [planeMap_sr, vertexAction_sr, ← ngonVertex_neg, ← ngonVertex_add, sub_eq_add_neg]

/-- The equivariance statement phrased with the `•` notation of the two `MulAction`s. -/
theorem smul_ngonVertex (g : DihedralGroup n) (k : ZMod n) :
    g • ngonVertex n k = ngonVertex n (g • k) :=
  PentagonPentagonEquivarianceGeneral n g k

/-- The pentagon case `n = 5` of the general equivariance theorem. -/
theorem pentagon_equivariance (g : DihedralGroup 5) (k : ZMod 5) :
    planeMap g (ngonVertex 5 k) = ngonVertex 5 (vertexAction g k) :=
  PentagonPentagonEquivarianceGeneral 5 g k

end Brockian

