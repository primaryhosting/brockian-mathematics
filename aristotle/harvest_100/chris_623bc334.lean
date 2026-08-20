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

set_option grind.warning false

namespace Brockian

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
indexed by `k : ZMod n`. -/
noncomputable def ngonVertex (n : ℕ) (k : ZMod n) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))

/-- The natural action of the dihedral group `DihedralGroup n` on the vertex indices
`ZMod n` of a regular `n`-gon: the rotation `r i` shifts indices, the reflection `sr i`
reverses them. -/
def ngonIndexAction (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r i, k => k - i
  | .sr i, k => i - k

/-- The geometric action of `DihedralGroup n` on the plane `ℂ`: rotations act by
multiplication by a root of unity, reflections by a rotated complex conjugation. -/
noncomputable def ngonPlaneAction (n : ℕ) : DihedralGroup n → ℂ → ℂ
  | .r i, z => ngonVertex n (-i) * z
  | .sr i, z => ngonVertex n i * (starRingEnd ℂ) z

section Lemmas

variable {n : ℕ}

/-- Two natural numbers congruent mod `n` give the same `n`-th root of unity. -/
lemma exp_nat_congr (hn : 0 < n) {a b : ℕ} (h : (a : ZMod n) = (b : ZMod n)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmod : a ≡ b [MOD n] := (ZMod.natCast_eq_natCast_iff a b n).mp h
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd (n := n) (a := a) (b := b)).mp hmod
  have hac : (b : ℂ) - (a : ℂ) = (n : ℂ) * (c : ℂ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℂ)) hc
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  have key : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) / (n : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ)
          + ((-c : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ)) / (n : ℂ) := by
    congr 1
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hac
  rw [key, add_div, mul_div_assoc, mul_div_assoc]
  field_simp

lemma ngonVertex_eq_exp_ofReal (n : ℕ) (k : ZMod n) :
    ngonVertex n k = Complex.exp (((2 * Real.pi * (k.val : ℝ) / (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  unfold ngonVertex
  congr 1
  push_cast
  ring

@[simp] lemma norm_ngonVertex (n : ℕ) (k : ZMod n) : ‖ngonVertex n k‖ = 1 := by
  rw [ngonVertex_eq_exp_ofReal]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ngonVertex_ne_zero (n : ℕ) (k : ZMod n) : ngonVertex n k ≠ 0 := by
  intro h
  have := norm_ngonVertex n k
  rw [h] at this
  simp at this

@[simp] lemma ngonVertex_zero (n : ℕ) : ngonVertex n 0 = 1 := by
  unfold ngonVertex
  simp

lemma ngonVertex_add (hn : 0 < n) (a b : ZMod n) :
    ngonVertex n (a + b) = ngonVertex n a * ngonVertex n b := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcast : (((a + b).val : ℕ) : ZMod n) = ((a.val + b.val : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_zmod_val]
    ring
  have h1 : ngonVertex n (a + b)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a.val + b.val : ℕ) : ℂ) / (n : ℂ)) :=
    exp_nat_congr hn hcast
  rw [h1]
  unfold ngonVertex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ngonVertex_neg (hn : 0 < n) (a : ZMod n) :
    ngonVertex n (-a) = (starRingEnd ℂ) (ngonVertex n a) := by
  have h1 : ngonVertex n (-a) * ngonVertex n a = 1 := by
    rw [← ngonVertex_add hn]
    simp
  rw [← Complex.inv_eq_conj (norm_ngonVertex n a)]
  exact eq_inv_of_mul_eq_one_left h1

lemma ngonVertex_sub (hn : 0 < n) (a b : ZMod n) :
    ngonVertex n (a - b) = ngonVertex n a * (starRingEnd ℂ) (ngonVertex n b) := by
  rw [sub_eq_add_neg, ngonVertex_add hn, ngonVertex_neg hn]

end Lemmas

/-- **Pentagon pentagon equivariance, general `n`-gon version.**

For every `n > 0`, the dihedral group `DihedralGroup n` acts both on the vertex index set
`ZMod n` of a regular `n`-gon and on the plane `ℂ` (rotations by `n`-th roots of unity,
reflections by conjugation composed with a rotation), and the vertex map
`k ↦ ngonVertex n k` intertwines the two actions.  The vertices all lie on the unit circle.

Specialising to `n = 5` recovers the `D₅` pentagon representation statement. -/
theorem PentagonPentagonEquivarianceGeneral (n : ℕ) (hn : 0 < n) :
    (∀ k : ZMod n, ngonIndexAction n 1 k = k) ∧
    (∀ g h : DihedralGroup n, ∀ k : ZMod n,
        ngonIndexAction n (g * h) k = ngonIndexAction n g (ngonIndexAction n h k)) ∧
    (∀ z : ℂ, ngonPlaneAction n 1 z = z) ∧
    (∀ g h : DihedralGroup n, ∀ z : ℂ,
        ngonPlaneAction n (g * h) z = ngonPlaneAction n g (ngonPlaneAction n h z)) ∧
    (∀ g : DihedralGroup n, ∀ k : ZMod n,
        ngonPlaneAction n g (ngonVertex n k) = ngonVertex n (ngonIndexAction n g k)) ∧
    (∀ k : ZMod n, ‖ngonVertex n k‖ = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [DihedralGroup.one_def]
    simp [ngonIndexAction]
  · rintro (i | i) (j | j) k <;>
      simp [ngonIndexAction, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring
  · intro z
    rw [DihedralGroup.one_def]
    simp [ngonPlaneAction]
  · rintro (i | i) (j | j) z
    · simp only [DihedralGroup.r_mul_r, ngonPlaneAction, neg_add]
      rw [ngonVertex_add hn]
      ring
    · simp only [DihedralGroup.r_mul_sr, ngonPlaneAction]
      rw [show j - i = j + -i by ring, ngonVertex_add hn]
      ring
    · simp only [DihedralGroup.sr_mul_r, ngonPlaneAction]
      rw [ngonVertex_add hn, ngonVertex_neg hn, map_mul, Complex.conj_conj]
      ring
    · simp only [DihedralGroup.sr_mul_sr, ngonPlaneAction]
      rw [show -(j - i) = i + -j by ring, ngonVertex_add hn, ngonVertex_neg hn, map_mul,
        Complex.conj_conj]
      ring
  · rintro (i | i) k
    · simp only [ngonPlaneAction, ngonIndexAction]
      rw [show k - i = -i + k by ring, ngonVertex_add hn]
    · simp only [ngonPlaneAction, ngonIndexAction]
      rw [ngonVertex_sub hn]
  · intro k
    exact norm_ngonVertex n k

/-- The original pentagon (`D₅`) case, obtained from the general theorem. -/
theorem PentagonPentagonEquivariance :
    (∀ g : DihedralGroup 5, ∀ k : ZMod 5,
        ngonPlaneAction 5 g (ngonVertex 5 k) = ngonVertex 5 (ngonIndexAction 5 g k)) ∧
    (∀ k : ZMod 5, ‖ngonVertex 5 k‖ = 1) :=
  ⟨(PentagonPentagonEquivarianceGeneral 5 (by norm_num)).2.2.2.2.1,
    (PentagonPentagonEquivarianceGeneral 5 (by norm_num)).2.2.2.2.2⟩

end Brockian

