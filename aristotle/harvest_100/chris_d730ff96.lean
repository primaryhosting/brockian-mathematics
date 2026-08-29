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

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)`, the rotation constant of the
regular `n`-gon. -/
noncomputable def ngonRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The vertices of the regular `n`-gon inscribed in the unit circle, indexed by `ZMod n`. -/
noncomputable def ngonVertex (n : ℕ) (k : ZMod n) : ℂ := (ngonRoot n) ^ (k.val)

/-- The combinatorial action of the dihedral group `D n` on the vertex labels `ZMod n`:
the rotation `r i` sends `k` to `k - i` and the reflection `sr i` sends `k` to `i - k`.
(The sign in the rotation matches Mathlib's multiplication convention for `DihedralGroup`.) -/
def dihedralVertexAction (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, k => k - i
  | DihedralGroup.sr i, k => i - k

/-- The geometric action of the dihedral group `D n` on the complex plane: `r i` acts by
the rotation through the angle `-2πi/n`, and `sr i` acts by a reflection in a symmetry axis
of the regular `n`-gon. -/
noncomputable def ngonRep (n : ℕ) : DihedralGroup n → ℂ → ℂ
  | DihedralGroup.r i, z => ngonVertex n (-i) * z
  | DihedralGroup.sr i, z => ngonVertex n i * (starRingEnd ℂ) z

section

variable {n : ℕ} [NeZero n]

lemma ngonRoot_pow_n : (ngonRoot n) ^ n = 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [ngonRoot, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * Real.pi * Complex.I / n) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [this]
  rw [show (2 : ℂ) * Real.pi * Complex.I = (2 * Real.pi : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I]
  simp

omit [NeZero n] in
lemma ngonRoot_ne_zero : (ngonRoot n) ≠ 0 := Complex.exp_ne_zero _

lemma ngonRoot_pow_mod (m : ℕ) : (ngonRoot n) ^ (m % n) = (ngonRoot n) ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, ngonRoot_pow_n, one_pow, one_mul]

omit [NeZero n] in
lemma abs_ngonRoot : ‖ngonRoot n‖ = 1 := by
  rw [ngonRoot, Complex.norm_exp]
  have : ((2 : ℂ) * Real.pi * Complex.I / n).re = 0 := by
    rw [show (2 : ℂ) * Real.pi * Complex.I / n
        = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  rw [this, Real.exp_zero]

/-- The vertex map is a homomorphism from `(ZMod n, +)` to the unit circle. -/
lemma ngonVertex_add (a b : ZMod n) :
    ngonVertex n (a + b) = ngonVertex n a * ngonVertex n b := by
  rw [ngonVertex, ngonVertex, ngonVertex, ZMod.val_add, ngonRoot_pow_mod, pow_add]

omit [NeZero n] in
lemma ngonVertex_zero : ngonVertex n 0 = 1 := by
  simp [ngonVertex]

omit [NeZero n] in
lemma ngonVertex_ne_zero (a : ZMod n) : ngonVertex n a ≠ 0 :=
  pow_ne_zero _ ngonRoot_ne_zero

lemma ngonVertex_neg (a : ZMod n) : ngonVertex n (-a) = (ngonVertex n a)⁻¹ := by
  have h : ngonVertex n (-a) * ngonVertex n a = 1 := by
    rw [← ngonVertex_add, neg_add_cancel, ngonVertex_zero]
  exact eq_inv_of_mul_eq_one_left h

/-- `ngonRoot n` is a primitive `n`-th root of unity. -/
lemma isPrimitiveRoot_ngonRoot : IsPrimitiveRoot (ngonRoot n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

/-- The regular `n`-gon really has `n` distinct vertices. -/
lemma ngonVertex_injective : Function.Injective (ngonVertex n) := by
  intro a b hab
  have h := isPrimitiveRoot_ngonRoot.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab
  have := congrArg (fun m : ℕ => (m : ZMod n)) h
  simpa [ZMod.natCast_val, ZMod.cast_id] using this

omit [NeZero n] in
lemma abs_ngonVertex (a : ZMod n) : ‖ngonVertex n a‖ = 1 := by
  rw [ngonVertex, norm_pow, abs_ngonRoot, one_pow]

lemma conj_ngonVertex (a : ZMod n) :
    (starRingEnd ℂ) (ngonVertex n a) = ngonVertex n (-a) := by
  rw [ngonVertex_neg]
  exact (Complex.inv_eq_conj (abs_ngonVertex a)).symm

omit [NeZero n] in
lemma ngonRep_r (i : ZMod n) (z : ℂ) :
    ngonRep n (DihedralGroup.r i) z = ngonVertex n (-i) * z := rfl

omit [NeZero n] in
lemma ngonRep_sr (i : ZMod n) (z : ℂ) :
    ngonRep n (DihedralGroup.sr i) z = ngonVertex n i * (starRingEnd ℂ) z := rfl

/-- The geometric action is a genuine action of the dihedral group. -/
lemma ngonRep_mul (g h : DihedralGroup n) (z : ℂ) :
    ngonRep n (g * h) z = ngonRep n g (ngonRep n h z) := by
  cases g with
  | r i =>
    cases h with
    | r j =>
      rw [DihedralGroup.r_mul_r, ngonRep_r, ngonRep_r, ngonRep_r,
        show -(i + j) = -i + -j by ring, ngonVertex_add]
      ring
    | sr j =>
      rw [DihedralGroup.r_mul_sr, ngonRep_sr, ngonRep_r, ngonRep_sr,
        show j - i = -i + j by ring, ngonVertex_add]
      ring
  | sr i =>
    cases h with
    | r j =>
      rw [DihedralGroup.sr_mul_r, ngonRep_sr, ngonRep_sr, ngonRep_r, map_mul, conj_ngonVertex,
        neg_neg, show i + j = i + j from rfl, ngonVertex_add]
      ring
    | sr j =>
      rw [DihedralGroup.sr_mul_sr, ngonRep_r, ngonRep_sr, ngonRep_sr, map_mul, conj_ngonVertex,
        Complex.conj_conj, show -(j - i) = i + -j by ring, ngonVertex_add]
      ring

omit [NeZero n] in
lemma ngonRep_one (z : ℂ) : ngonRep n (1 : DihedralGroup n) z = z := by
  show ngonRep n (DihedralGroup.r 0) z = z
  rw [ngonRep_r, neg_zero, ngonVertex_zero, one_mul]

omit [NeZero n] in
/-- The combinatorial action is a genuine action of the dihedral group. -/
lemma dihedralVertexAction_mul (g h : DihedralGroup n) (k : ZMod n) :
    dihedralVertexAction n (g * h) k
      = dihedralVertexAction n g (dihedralVertexAction n h k) := by
  cases g with
  | r i => cases h with
    | r j =>
      simp only [DihedralGroup.r_mul_r, dihedralVertexAction]; ring
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, dihedralVertexAction]; ring
  | sr i => cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, dihedralVertexAction]; ring
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, dihedralVertexAction]; ring

omit [NeZero n] in
lemma dihedralVertexAction_one (k : ZMod n) :
    dihedralVertexAction n (1 : DihedralGroup n) k = k := by
  show dihedralVertexAction n (DihedralGroup.r 0) k = k
  simp [dihedralVertexAction]

omit [NeZero n] in
/-- The geometric action preserves absolute values (it acts by isometries fixing the origin). -/
lemma norm_ngonRep (g : DihedralGroup n) (z : ℂ) : ‖ngonRep n g z‖ = ‖z‖ := by
  cases g with
  | r i => rw [ngonRep_r, norm_mul, abs_ngonVertex, one_mul]
  | sr i => rw [ngonRep_sr, norm_mul, abs_ngonVertex, one_mul, RCLike.norm_conj]

end

/-- **Pentagon equivariance, general `n`-gon version.**

For every `n ≥ 1`, the assignment `ngonRep n` is an action of the dihedral group `D n` on the
complex plane by norm-preserving maps, `dihedralVertexAction n` is the corresponding action on the
vertex labels `ZMod n`, and the vertex map `ngonVertex n : ZMod n → ℂ` of the regular `n`-gon is
equivariant for these two actions.  Specialising to `n = 5` recovers the pentagon (`D₅`) statement.
-/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) [NeZero n] :
    (∀ g h : DihedralGroup n, ∀ z : ℂ, ngonRep n (g * h) z = ngonRep n g (ngonRep n h z)) ∧
    (∀ z : ℂ, ngonRep n (1 : DihedralGroup n) z = z) ∧
    (∀ g : DihedralGroup n, ∀ z : ℂ, ‖ngonRep n g z‖ = ‖z‖) ∧
    (∀ g h : DihedralGroup n, ∀ k : ZMod n,
        dihedralVertexAction n (g * h) k
          = dihedralVertexAction n g (dihedralVertexAction n h k)) ∧
    (∀ g : DihedralGroup n, ∀ k : ZMod n,
        ngonRep n g (ngonVertex n k) = ngonVertex n (dihedralVertexAction n g k)) ∧
    Function.Injective (ngonVertex n) := by
  refine ⟨ngonRep_mul, ngonRep_one, norm_ngonRep, dihedralVertexAction_mul, ?_,
    ngonVertex_injective⟩
  intro g k
  cases g with
  | r i =>
    rw [ngonRep_r, ← ngonVertex_add, dihedralVertexAction, show -i + k = k - i by ring]
  | sr i =>
    rw [ngonRep_sr, conj_ngonVertex, ← ngonVertex_add, dihedralVertexAction, sub_eq_add_neg]

/-- The pentagon case `n = 5` of `PentagonPentagonEquivarianceGeneral`: the `D₅`-action on the
plane is equivariant with respect to the labelling of the five vertices of the regular pentagon. -/
theorem PentagonEquivariance_five (g : DihedralGroup 5) (k : ZMod 5) :
    ngonRep 5 g (ngonVertex 5 k) = ngonVertex 5 (dihedralVertexAction 5 g k) :=
  (PentagonPentagonEquivarianceGeneral 5).2.2.2.2.1 g k

end Brockian

