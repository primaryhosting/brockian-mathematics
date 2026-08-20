/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

/-- The primitive `n`-th root of unity `exp (2 π i / n)`, the basic rotation of a regular
`n`-gon inscribed in the unit circle of `ℂ`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

/-- The `k`-th vertex of the regular `n`-gon, indexed by `ZMod n`. -/
noncomputable def vertex (n : ℕ) (k : ZMod n) : ℂ := zeta n ^ k.val

/-- The combinatorial action of the dihedral group `D n` on the vertex labels `ZMod n`:
the rotation `r i` shifts labels by `i`, and the reflection `sr i` sends `k` to `-k - i`. -/
def idxAct {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | .r i, k => k + i
  | .sr i, k => -k - i

/-- The geometric action of the dihedral group `D n` on the plane `ℂ`: the rotation `r i` is
multiplication by `ζ^i`, and the reflection `sr i` is `z ↦ conj (ζ^i * z)`. -/
noncomputable def geoAct {n : ℕ} : DihedralGroup n → ℂ → ℂ
  | .r i, z => vertex n i * z
  | .sr i, z => (starRingEnd ℂ) (vertex n i * z)

section
variable {n : ℕ} [NeZero n]

lemma zeta_pow_n : zeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).pow_eq_one

omit [NeZero n] in
lemma zeta_ne_zero : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_mod (m : ℕ) : zeta n ^ (m % n) = zeta n ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, zeta_pow_n, one_pow, one_mul]

lemma vertex_natCast (m : ℕ) : vertex n (m : ZMod n) = zeta n ^ m := by
  rw [vertex, ZMod.val_natCast, zeta_pow_mod]

lemma vertex_add (a b : ZMod n) : vertex n (a + b) = vertex n a * vertex n b := by
  rw [vertex, vertex, vertex, ZMod.val_add, zeta_pow_mod, pow_add]

omit [NeZero n] in
lemma vertex_zero : vertex n 0 = 1 := by
  rw [vertex, ZMod.val_zero, pow_zero]

omit [NeZero n] in
lemma vertex_ne_zero (k : ZMod n) : vertex n k ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma vertex_mul_neg (k : ZMod n) : vertex n k * vertex n (-k) = 1 := by
  rw [← vertex_add, add_neg_cancel, vertex_zero]

omit [NeZero n] in
lemma conj_zeta : (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

lemma conj_vertex (k : ZMod n) : (starRingEnd ℂ) (vertex n k) = vertex n (-k) := by
  have h : (starRingEnd ℂ) (vertex n k) * vertex n k = 1 := by
    rw [vertex, map_pow, conj_zeta, ← mul_pow, inv_mul_cancel₀ zeta_ne_zero, one_pow]
  have h2 : vertex n (-k) * vertex n k = 1 := by
    rw [mul_comm]; exact vertex_mul_neg k
  exact mul_right_cancel₀ (vertex_ne_zero k) (h.trans h2.symm)

omit [NeZero n] in
lemma norm_zeta : ‖zeta n‖ = 1 := by
  simp [zeta, Complex.norm_exp, Complex.div_re]

omit [NeZero n] in
/-- Every vertex of the regular `n`-gon lies on the unit circle. -/
lemma norm_vertex (k : ZMod n) : ‖vertex n k‖ = 1 := by
  rw [vertex, norm_pow, norm_zeta, one_pow]

omit [NeZero n] in
/-- `idxAct` is a genuine left action of `D n` on the labels. -/
lemma idxAct_one (k : ZMod n) : idxAct (1 : DihedralGroup n) k = k := by
  rw [DihedralGroup.one_def]
  simp [idxAct]

omit [NeZero n] in
lemma idxAct_mul (g h : DihedralGroup n) (k : ZMod n) :
    idxAct (g * h) k = idxAct g (idxAct h k) := by
  cases g with
  | r i =>
    cases h with
    | r j => simp only [DihedralGroup.r_mul_r, idxAct]; ring
    | sr j => simp only [DihedralGroup.r_mul_sr, idxAct]; ring
  | sr i =>
    cases h with
    | r j => simp only [DihedralGroup.sr_mul_r, idxAct]; ring
    | sr j => simp only [DihedralGroup.sr_mul_sr, idxAct]; ring

omit [NeZero n] in
/-- `geoAct` is a genuine left action of `D n` on the plane. -/
lemma geoAct_one (z : ℂ) : geoAct (1 : DihedralGroup n) z = z := by
  rw [DihedralGroup.one_def]
  simp [geoAct, vertex_zero]

lemma geoAct_mul (g h : DihedralGroup n) (z : ℂ) :
    geoAct (g * h) z = geoAct g (geoAct h z) := by
  cases g with
  | r i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.r_mul_r, geoAct, vertex_add]
      ring
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, geoAct, map_mul, conj_vertex]
      rw [show -(j - i) = i + -j by ring, vertex_add]
      ring
  | sr i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, geoAct, vertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, geoAct, map_mul, conj_vertex,
        Complex.conj_conj]
      rw [neg_neg, show j - i = -i + j by ring, vertex_add]
      ring

/-- The `n` vertices are pairwise distinct, i.e. they really do form a regular `n`-gon. -/
lemma vertex_injective : Function.Injective (vertex n) := by
  intro a b hab
  have := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).pow_inj
    (ZMod.val_lt a) (ZMod.val_lt b) hab
  exact (ZMod.val_injective n) this

/-- **Pentagon equivariance, general `n`-gon version.**  The vertex map
`k ↦ ζ^k` from the labels `ZMod n` to the plane intertwines the combinatorial action of the
dihedral group `D n` on the labels with its geometric action (rotations and reflections)
on the plane `ℂ`.  For `n = 5` this is the classical `D₅` pentagon statement. -/
theorem PentagonPentagonEquivarianceGeneral (g : DihedralGroup n) (k : ZMod n) :
    geoAct g (vertex n k) = vertex n (idxAct g k) := by
  cases g with
  | r i =>
    simp only [geoAct, idxAct, vertex_add]
    ring
  | sr i =>
    simp only [geoAct, idxAct, ← vertex_add, conj_vertex]
    rw [sub_eq_add_neg, neg_add_rev]

/-- The classical pentagon case `n = 5`. -/
theorem PentagonEquivarianceD5 (g : DihedralGroup 5) (k : ZMod 5) :
    geoAct g (vertex 5 k) = vertex 5 (idxAct g k) :=
  PentagonPentagonEquivarianceGeneral g k

end

end Brockian

