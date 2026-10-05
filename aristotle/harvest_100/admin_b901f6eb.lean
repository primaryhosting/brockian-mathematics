/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring `/-!  -/` to precede `import`, so the header
is repeated below as the module docstring, verbatim.)
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

open DihedralGroup Complex

/-! ## Vertices of a regular `n`-gon

The `k`-th vertex of the standard regular `n`-gon inscribed in the unit circle of `ℂ` is
`exp (2 π i k / n)`.  This only depends on `k` modulo `n`, so it is naturally indexed by
`ZMod n`; Mathlib already packages this as the additive character `ZMod.toCircle`.
-/

/-- The `k`-th vertex of the standard regular `n`-gon, as a complex number.
It equals `exp (2 * π * I * k / n)` (see `Brockian.ngonVertex_eq_exp`). -/
noncomputable def ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  (ZMod.toCircle k : Circle)

theorem ngonVertex_eq_exp (n : ℕ) [NeZero n] (k : ZMod n) :
    ngonVertex n k = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / (n : ℂ)) :=
  ZMod.toCircle_apply k

theorem ngonVertex_add (n : ℕ) [NeZero n] (i k : ZMod n) :
    ngonVertex n (i + k) = ngonVertex n i * ngonVertex n k := by
  simp [ngonVertex, AddChar.map_add_eq_mul]

theorem ngonVertex_neg (n : ℕ) [NeZero n] (k : ZMod n) :
    ngonVertex n (-k) = (starRingEnd ℂ) (ngonVertex n k) := by
  rw [ngonVertex, ngonVertex, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem ngonVertex_zero (n : ℕ) [NeZero n] : ngonVertex n 0 = 1 := by
  simp [ngonVertex]

theorem norm_ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) : ‖ngonVertex n k‖ = 1 :=
  Circle.norm_coe _

/-! ## The two dihedral actions -/

/-- The combinatorial action of the dihedral group `D_n` on the vertex labels `ZMod n`:
the rotation `r i` shifts labels by `i`, and the reflection `sr i` sends `k` to `-i - k`.
(The signs are dictated by Mathlib's multiplication convention on `DihedralGroup n`.) -/
def dihedralIdx (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => k + i
  | DihedralGroup.sr i, k => -i - k

/-- The geometric action of the dihedral group `D_n` on the plane `ℂ`: the rotation `r i`
multiplies by the root of unity `ngonVertex n i`, and the reflection `sr i` is the composition
of that rotation with complex conjugation. -/
noncomputable def dihedralPlane (n : ℕ) [NeZero n] : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => ngonVertex n i * z
  | DihedralGroup.sr i, z => (starRingEnd ℂ) (ngonVertex n i * z)

theorem dihedralIdx_one (n : ℕ) (k : ZMod n) : dihedralIdx n 1 k = k := by
  rw [DihedralGroup.one_def]
  simp [dihedralIdx]

theorem dihedralPlane_one (n : ℕ) [NeZero n] (z : ℂ) : dihedralPlane n 1 z = z := by
  rw [DihedralGroup.one_def]
  simp [dihedralPlane, ngonVertex_zero]

theorem dihedralIdx_mul (n : ℕ) (g h : DihedralGroup n) (k : ZMod n) :
    dihedralIdx n (g * h) k = dihedralIdx n g (dihedralIdx n h k) := by
  cases g with
  | r i =>
    cases h with
    | r j => simp only [DihedralGroup.r_mul_r, dihedralIdx]; ring
    | sr j => simp only [DihedralGroup.r_mul_sr, dihedralIdx]; ring
  | sr i =>
    cases h with
    | r j => simp only [DihedralGroup.sr_mul_r, dihedralIdx]; ring
    | sr j => simp only [DihedralGroup.sr_mul_sr, dihedralIdx]; ring

theorem dihedralPlane_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (z : ℂ) :
    dihedralPlane n (g * h) z = dihedralPlane n g (dihedralPlane n h z) := by
  have hadd : ∀ i j : ZMod n, ngonVertex n (i + j) = ngonVertex n i * ngonVertex n j :=
    ngonVertex_add n
  have hsub : ∀ i j : ZMod n,
      ngonVertex n (i - j) = ngonVertex n i * (starRingEnd ℂ) (ngonVertex n j) := by
    intro i j
    rw [sub_eq_add_neg, hadd, ngonVertex_neg]
  cases g with
  | r i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.r_mul_r, dihedralPlane, hadd]; ring
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, dihedralPlane, hsub, map_mul,
        Complex.conj_conj]
      ring
  | sr i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, dihedralPlane, hadd, map_mul]
      ring
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, dihedralPlane, hsub, map_mul,
        Complex.conj_conj]
      ring

/-- Every element of the dihedral group acts on the plane by a norm-preserving map. -/
theorem norm_dihedralPlane (n : ℕ) [NeZero n] (g : DihedralGroup n) (z : ℂ) :
    ‖dihedralPlane n g z‖ = ‖z‖ := by
  cases g with
  | r i => simp [dihedralPlane, norm_ngonVertex]
  | sr i => simp [dihedralPlane, norm_ngonVertex]

/-- Every element of the dihedral group acts on the plane by an `ℝ`-linear map. -/
theorem dihedralPlane_linear (n : ℕ) [NeZero n] (g : DihedralGroup n) (a b : ℝ) (z w : ℂ) :
    dihedralPlane n g ((a : ℂ) * z + (b : ℂ) * w) =
      (a : ℂ) * dihedralPlane n g z + (b : ℂ) * dihedralPlane n g w := by
  cases g with
  | r i => simp only [dihedralPlane]; ring
  | sr i =>
    simp only [dihedralPlane, map_add, map_mul, Complex.conj_ofReal]
    ring

/-! ## The general equivariance theorem -/

/--
**Pentagon equivariance, in general.**  For every `n ≥ 1` the labelling map
`k ↦ ngonVertex n k` sending a vertex label of the regular `n`-gon to the corresponding point
`exp (2 π i k / n)` of the plane intertwines the combinatorial action of the dihedral group
`D_n` on the labels `ZMod n` with its geometric action on `ℂ`.

The statement records that both are genuine (left) actions of `DihedralGroup n` — they send
`1` to the identity and products to composites — and that the vertex map is equivariant.
Taking `n = 5` recovers the pentagon (`D_5`) case, see
`Brockian.pentagon_equivariance`.
-/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n] :
    (∀ k : ZMod n, dihedralIdx n 1 k = k) ∧
    (∀ z : ℂ, dihedralPlane n 1 z = z) ∧
    (∀ (g h : DihedralGroup n) (k : ZMod n),
      dihedralIdx n (g * h) k = dihedralIdx n g (dihedralIdx n h k)) ∧
    (∀ (g h : DihedralGroup n) (z : ℂ),
      dihedralPlane n (g * h) z = dihedralPlane n g (dihedralPlane n h z)) ∧
    (∀ (g : DihedralGroup n) (k : ZMod n),
      dihedralPlane n g (ngonVertex n k) = ngonVertex n (dihedralIdx n g k)) := by
  refine ⟨dihedralIdx_one n, dihedralPlane_one n, dihedralIdx_mul n, dihedralPlane_mul n, ?_⟩
  intro g k
  cases g with
  | r i =>
    simp only [dihedralPlane, dihedralIdx, ngonVertex_add]
    ring
  | sr i =>
    have : (-i - k : ZMod n) = -(i + k) := by ring
    simp only [dihedralPlane, dihedralIdx, this, ngonVertex_neg, ngonVertex_add]

/-- The pentagon case `n = 5` of `Brockian.PentagonPentagonEquivarianceGeneral`: the map
sending the label `k ∈ ZMod 5` to the fifth root of unity `exp (2 π i k / 5)` is
`D_5`-equivariant. -/
theorem pentagon_equivariance (g : DihedralGroup 5) (k : ZMod 5) :
    dihedralPlane 5 g (ngonVertex 5 k) = ngonVertex 5 (dihedralIdx 5 g k) :=
  (PentagonPentagonEquivarianceGeneral 5).2.2.2.2 g k

/-- The vertices of the regular `n`-gon are exactly the `n`-th roots of unity. -/
theorem ngonVertex_pow (n : ℕ) [NeZero n] (k : ZMod n) : (ngonVertex n k) ^ n = 1 := by
  have : ((ZMod.toCircle k) ^ n : Circle) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  calc (ngonVertex n k) ^ n = (((ZMod.toCircle k) ^ n : Circle) : ℂ) := by
        simp [ngonVertex]
    _ = 1 := by rw [this]; simp

end Brockian

