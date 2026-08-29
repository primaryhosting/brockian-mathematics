/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the identical module docstring is repeated below.)
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
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Complex DihedralGroup

/-!
## Setup

We generalize the `D₅` pentagon representation picture to an arbitrary regular `n`-gon.

* The vertices of the regular `n`-gon are labelled by `ZMod n`; the geometric realization of the
  vertex `k` is the complex number `ngonVertex n k = exp (2 π I k / n)`, obtained from Mathlib's
  additive character `ZMod.toCircle`.
* `ngonAct` is the combinatorial action of `DihedralGroup n` on the vertex labels `ZMod n`.
* `ngonSymm` is the geometric action of `DihedralGroup n` on `ℂ` by rotations `z ↦ ζₙ^i * z` and
  reflections `z ↦ ζₙ^(-i) * conj z`.

The main theorem `PentagonPentagonEquivarianceGeneral` says that the vertex realization map
intertwines these two actions, i.e. it is `DihedralGroup n`-equivariant.

The analytic content is supplied entirely by existing Mathlib results about the additive character
`ZMod.toCircle` (`Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`), namely
`AddChar.map_add_eq_mul`, `AddChar.map_neg_eq_inv`, `Circle.coe_inv_eq_conj` and
`ZMod.injective_toCircle`.
-/

/-- The geometric realization of the vertex `k` of the regular `n`-gon:
`ngonVertex n k = exp (2 * π * I * k / n)`. -/
noncomputable def ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) : ℂ :=
  (ZMod.toCircle k : Circle)

/-- The combinatorial action of the dihedral group on the vertex labels of the `n`-gon:
the rotation `r i` sends the label `k` to `i + k`, and the reflection `sr i` sends `k` to
`-i - k`. -/
def ngonAct {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => i + k
  | DihedralGroup.sr i, k => -i - k

/-- The geometric action of the dihedral group on the complex plane: the rotation `r i` acts as
multiplication by `ζₙ^i`, and the reflection `sr i` acts as `z ↦ ζₙ^(-i) * conj z`. -/
noncomputable def ngonSymm (n : ℕ) [NeZero n] : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => ngonVertex n i * z
  | DihedralGroup.sr i, z => ngonVertex n (-i) * (starRingEnd ℂ) z

/-!
## Basic properties of the vertex map
-/

theorem ngonVertex_eq_exp (n : ℕ) [NeZero n] (j : ℤ) :
    ngonVertex n (j : ZMod n) = Complex.exp (2 * π * Complex.I * j / n) := by
  simpa [ngonVertex] using ZMod.toCircle_intCast (N := n) j

@[simp]
theorem ngonVertex_zero (n : ℕ) [NeZero n] : ngonVertex n 0 = 1 := by
  simp [ngonVertex]

theorem ngonVertex_add (n : ℕ) [NeZero n] (a b : ZMod n) :
    ngonVertex n (a + b) = ngonVertex n a * ngonVertex n b := by
  rw [ngonVertex, ngonVertex, ngonVertex, AddChar.map_add_eq_mul]
  push_cast
  ring

theorem ngonVertex_neg (n : ℕ) [NeZero n] (a : ZMod n) :
    ngonVertex n (-a) = (starRingEnd ℂ) (ngonVertex n a) := by
  rw [ngonVertex, ngonVertex, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem ngonVertex_sub (n : ℕ) [NeZero n] (a b : ZMod n) :
    ngonVertex n (a - b) = ngonVertex n a * (starRingEnd ℂ) (ngonVertex n b) := by
  rw [sub_eq_add_neg, ngonVertex_add, ngonVertex_neg]

@[simp]
theorem abs_ngonVertex (n : ℕ) [NeZero n] (k : ZMod n) : ‖ngonVertex n k‖ = 1 := by
  simp [ngonVertex]

theorem ngonVertex_injective (n : ℕ) [NeZero n] : Function.Injective (ngonVertex n) := by
  intro a b hab
  exact ZMod.injective_toCircle (Subtype.ext hab)

/-!
## The two actions are genuine group actions
-/

@[simp]
theorem ngonAct_one {n : ℕ} (k : ZMod n) : ngonAct (1 : DihedralGroup n) k = k := by
  show ngonAct (DihedralGroup.r 0) k = k
  simp [ngonAct]

theorem ngonAct_mul {n : ℕ} (g h : DihedralGroup n) (k : ZMod n) :
    ngonAct (g * h) k = ngonAct g (ngonAct h k) := by
  cases g with
  | r i => cases h with
    | r j => simp [ngonAct, add_assoc]
    | sr j => simp [ngonAct]; ring
  | sr i => cases h with
    | r j => simp [ngonAct]; ring
    | sr j => simp [ngonAct]; ring

@[simp]
theorem ngonSymm_one (n : ℕ) [NeZero n] (z : ℂ) : ngonSymm n (1 : DihedralGroup n) z = z := by
  show ngonSymm n (DihedralGroup.r 0) z = z
  simp [ngonSymm]

theorem ngonSymm_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (z : ℂ) :
    ngonSymm n (g * h) z = ngonSymm n g (ngonSymm n h z) := by
  cases g with
  | r i =>
    cases h with
    | r j => simp [ngonSymm, ngonVertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, ngonSymm]
      rw [show -(j - i) = i + -j by ring, ngonVertex_add, mul_assoc]
  | sr i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, ngonSymm, map_mul, ← ngonVertex_neg]
      rw [show -(i + j) = -i + -j by ring, ngonVertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, ngonSymm, map_mul, ← ngonVertex_neg, neg_neg,
        Complex.conj_conj]
      rw [show j - i = -i + j by ring, ngonVertex_add, mul_assoc]

/-!
## Main theorem: equivariance of the vertex realization map
-/

/-- **Pentagon equivariance, generalized to arbitrary `n`-gons.**

The realization map sending the vertex label `k : ZMod n` of the regular `n`-gon to the complex
number `exp (2 π I k / n)` intertwines the combinatorial action `ngonAct` of the dihedral group
`DihedralGroup n` on the labels with the geometric action `ngonSymm` on `ℂ` by rotations and
reflections.  For `n = 5` this is the classical `D₅` pentagon representation statement. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n] (g : DihedralGroup n)
    (k : ZMod n) :
    ngonVertex n (ngonAct g k) = ngonSymm n g (ngonVertex n k) := by
  cases g with
  | r i => simp [ngonAct, ngonSymm, ngonVertex_add]
  | sr i =>
    simp only [ngonAct, ngonSymm]
    rw [show -i - k = -i + -k by ring, ngonVertex_add, ngonVertex_neg n k]

/-- The pentagon case `n = 5`: the original `D₅` statement. -/
theorem PentagonEquivariance (g : DihedralGroup 5) (k : ZMod 5) :
    ngonVertex 5 (ngonAct g k) = ngonSymm 5 g (ngonVertex 5 k) :=
  PentagonPentagonEquivarianceGeneral 5 g k

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

