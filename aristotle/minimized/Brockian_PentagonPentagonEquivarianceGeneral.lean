/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

open Complex DihedralGroup

/-! ## Vertices of the regular `n`-gon

The vertices of the regular `n`-gon inscribed in the unit circle of `ℂ` are indexed by
`ZMod n`; the vertex with index `k` is `exp (2 * π * I * k / n)`.  We use Mathlib's additive
character `ZMod.toCircle : AddChar (ZMod N) Circle`, so that the "rotation" identity
`vertex (a + b) = vertex a * vertex b` is inherited from `AddChar.map_add_eq_mul`. -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
namely `exp (2 * π * I * k / n)`. -/

noncomputable def vertex (n : ℕ) [NeZero n] (k : ZMod n) : ℂ := (ZMod.toCircle k : ℂ)

variable {n : ℕ} [NeZero n]

@[simp] lemma vertex_zero : vertex n 0 = 1 := by simp [vertex]

@[simp] lemma vertex_add (a b : ZMod n) : vertex n (a + b) = vertex n a * vertex n b := by
  simp [vertex, AddChar.map_add_eq_mul]

@[simp] lemma vertex_neg (k : ZMod n) : vertex n (-k) = (starRingEnd ℂ) (vertex n k) := by
  rw [vertex, vertex, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma vertex_injective : Function.Injective (vertex n) := by
  intro a b hab
  exact ZMod.injective_toCircle (Subtype.ext hab)

/-! ## The dihedral group acting on vertex indices and on the plane -/

/-- The action of the dihedral group `DihedralGroup n` on the vertex indices `ZMod n`:
the rotation `r i` sends the index `k` to `k + i`, and the reflection `sr i` sends `k`
to `-(k + i)`. -/

def dihedralAct (g : DihedralGroup n) (k : ZMod n) : ZMod n :=
  match g with
  | r i => k + i
  | sr i => -(k + i)

/-- The geometric representation of `DihedralGroup n` on the plane `ℂ`: the rotation `r i`
acts as multiplication by the root of unity `exp (2 * π * I * i / n)`, and the reflection
`sr i` acts as `z ↦ conj (exp (2 * π * I * i / n) * z)`. -/

noncomputable def dihedralRep (g : DihedralGroup n) (z : ℂ) : ℂ :=
  match g with
  | r i => vertex n i * z
  | sr i => (starRingEnd ℂ) (vertex n i * z)

omit [NeZero n] in

@[simp] lemma dihedralRep_r (i : ZMod n) (z : ℂ) : dihedralRep (r i) z = vertex n i * z := rfl

@[simp] lemma dihedralRep_sr (i : ZMod n) (z : ℂ) :
    dihedralRep (sr i) z = (starRingEnd ℂ) (vertex n i * z) := rfl

omit [NeZero n] in

lemma dihedralAct_one (k : ZMod n) : dihedralAct (1 : DihedralGroup n) k = k := by
  show k + 0 = k
  exact add_zero k

omit [NeZero n] in

lemma dihedralAct_mul (g h : DihedralGroup n) (k : ZMod n) :
    dihedralAct (g * h) k = dihedralAct g (dihedralAct h k) := by
  cases g <;> cases h <;> simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, dihedralAct] <;> ring

lemma dihedralRep_one (z : ℂ) : dihedralRep (1 : DihedralGroup n) z = z := by
  show vertex n 0 * z = z
  rw [vertex_zero, one_mul]

lemma dihedralRep_mul (g h : DihedralGroup n) (z : ℂ) :
    dihedralRep (g * h) z = dihedralRep g (dihedralRep h z) := by
  cases g with
  | r i =>
    cases h with
    | r j =>
      simp only [r_mul_r, dihedralRep_r, vertex_add]
      ring
    | sr j =>
      simp only [r_mul_sr, dihedralRep_sr, dihedralRep_r, map_mul]
      rw [sub_eq_add_neg, vertex_add, vertex_neg, map_mul, Complex.conj_conj]
      ring
  | sr i =>
    cases h with
    | r j =>
      simp only [sr_mul_r, dihedralRep_sr, dihedralRep_r, map_mul, vertex_add]
      ring
    | sr j =>
      simp only [sr_mul_sr, dihedralRep_sr, dihedralRep_r, map_mul,
        Complex.conj_conj]
      rw [sub_eq_add_neg, vertex_add, vertex_neg]
      ring

/-- Every element of the dihedral group acts on the plane by an isometry (indeed by a
norm-preserving map). -/

lemma norm_dihedralRep (g : DihedralGroup n) (z : ℂ) : ‖dihedralRep g z‖ = ‖z‖ := by
  cases g <;> simp

/-- **Pentagon equivariance, in general.**  For every `n ≥ 1`, the geometric representation
`dihedralRep` of the dihedral group `DihedralGroup n` on the plane `ℂ` and the combinatorial
action `dihedralAct` on the vertex indices `ZMod n` are intertwined by the vertex map
`vertex n : ZMod n → ℂ` of the regular `n`-gon.  Precisely:

* `dihedralAct` is a group action on `ZMod n`;
* `dihedralRep` is a group action on `ℂ` by norm-preserving maps;
* the vertex map is injective and equivariant: `dihedralRep g (vertex n k) = vertex n (dihedralAct g k)`.

Taking `n = 5` recovers the pentagon (`D₅`) statement. -/

theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n] :
    (∀ k : ZMod n, dihedralAct (1 : DihedralGroup n) k = k) ∧
    (∀ (g h : DihedralGroup n) (k : ZMod n),
        dihedralAct (g * h) k = dihedralAct g (dihedralAct h k)) ∧
    (∀ z : ℂ, dihedralRep (1 : DihedralGroup n) z = z) ∧
    (∀ (g h : DihedralGroup n) (z : ℂ),
        dihedralRep (g * h) z = dihedralRep g (dihedralRep h z)) ∧
    (∀ (g : DihedralGroup n) (z : ℂ), ‖dihedralRep g z‖ = ‖z‖) ∧
    Function.Injective (vertex n) ∧
    (∀ (g : DihedralGroup n) (k : ZMod n),
        dihedralRep g (vertex n k) = vertex n (dihedralAct g k)) := by
  refine ⟨dihedralAct_one, dihedralAct_mul, dihedralRep_one, dihedralRep_mul,
    norm_dihedralRep, vertex_injective, ?_⟩
  intro g k
  cases g with
  | r i => simp [mul_comm]
  | sr i => simp [add_comm, mul_comm]

/-- The pentagon case `n = 5` of `PentagonPentagonEquivarianceGeneral`. -/
