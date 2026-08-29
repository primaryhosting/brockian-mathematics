/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

namespace Phys

/-! ### The 18 vectors

We use the Cabello–Estebaranz–García-Alcaine 18-vector, 9-basis Kochen–Specker set in `ℝ⁴`.
The vectors have integer coordinates, listed here as rows. -/

/-- Integer coordinates of the 18 Kochen–Specker vectors. -/
def ksCoord : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 0], ![1, -1, 0, 0], ![0, 1, 0, 0],
    ![1, 0, 1, 0], ![1, 0, -1, 0], ![1, -1, 1, -1], ![1, -1, -1, 1], ![0, 0, 1, 1],
    ![1, 1, 1, 1], ![0, 1, 0, -1], ![1, 0, 0, 1], ![1, 0, 0, -1], ![0, 1, -1, 0],
    ![1, 1, -1, 1], ![1, 1, 1, -1], ![-1, 1, 1, 1]]

/-- The 18 Kochen–Specker vectors, as vectors of the Euclidean space `ℝ⁴`. -/
noncomputable def ksVec (i : Fin 18) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((ksCoord i k : ℤ) : ℝ))

/-- The integer dot product of two of the 18 vectors. -/
def ksDot (i j : Fin 18) : ℤ := ∑ k, ksCoord i k * ksCoord j k

lemma inner_ksVec (i j : Fin 18) : inner ℝ (ksVec i) (ksVec j) = ((ksDot i j : ℤ) : ℝ) := by
  simp [ksVec, ksDot, PiLp.inner_apply, mul_comm]

lemma ksVec_orthogonal {i j : Fin 18} (h : ksDot i j = 0) :
    inner ℝ (ksVec i) (ksVec j) = 0 := by
  rw [inner_ksVec, h]
  simp

/-- All 18 vectors are nonzero, so four pairwise orthogonal ones really do form a basis of `ℝ⁴`. -/
lemma ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  have hd : ∀ i : Fin 18, ksDot i i ≠ 0 := by decide
  intro h
  have h0 : inner ℝ (ksVec i) (ksVec i) = ((ksDot i i : ℤ) : ℝ) := inner_ksVec i i
  rw [h] at h0
  simp only [inner_zero_left] at h0
  exact hd i (by exact_mod_cast h0.symm)

/-! ### `{0,1}`-colorings -/

/-- A `{0,1}`-coloring (in the sense of Kochen–Specker) of the 18 vectors: no two orthogonal
vectors are both colored `1`, and in every orthogonal basis of `ℝ⁴` formed by four of the
vectors at least one is colored `1`. -/
def IsKSColoring (f : Fin 18 → Bool) : Prop :=
  (∀ i j : Fin 18, inner ℝ (ksVec i) (ksVec j) = 0 → f i = true → f j = true → False) ∧
  (∀ i j k l : Fin 18,
      inner ℝ (ksVec i) (ksVec j) = 0 → inner ℝ (ksVec i) (ksVec k) = 0 →
      inner ℝ (ksVec i) (ksVec l) = 0 → inner ℝ (ksVec j) (ksVec k) = 0 →
      inner ℝ (ksVec j) (ksVec l) = 0 → inner ℝ (ksVec k) (ksVec l) = 0 →
      f i = true ∨ f j = true ∨ f k = true ∨ f l = true)

/-- The numerical value (`0` or `1`) of a coloring. -/
def colVal (f : Fin 18 → Bool) (i : Fin 18) : ℕ := if f i = true then 1 else 0

/-- In each of the nine orthogonal bases, exactly one vector is colored `1`. -/
lemma ctx_sum_eq_one {f : Fin 18 → Bool} (hf : IsKSColoring f) (a b c d : Fin 18)
    (h : ksDot a b = 0 ∧ ksDot a c = 0 ∧ ksDot a d = 0 ∧ ksDot b c = 0 ∧ ksDot b d = 0 ∧
      ksDot c d = 0) :
    colVal f a + colVal f b + colVal f c + colVal f d = 1 := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h
  obtain ⟨hexcl, hbasis⟩ := hf
  have hone := hbasis a b c d (ksVec_orthogonal hab) (ksVec_orthogonal hac)
    (ksVec_orthogonal had) (ksVec_orthogonal hbc) (ksVec_orthogonal hbd) (ksVec_orthogonal hcd)
  have eab := hexcl a b (ksVec_orthogonal hab)
  have eac := hexcl a c (ksVec_orthogonal hac)
  have ead := hexcl a d (ksVec_orthogonal had)
  have ebc := hexcl b c (ksVec_orthogonal hbc)
  have ebd := hexcl b d (ksVec_orthogonal hbd)
  have ecd := hexcl c d (ksVec_orthogonal hcd)
  unfold colVal
  cases ha : f a <;> cases hb : f b <;> cases hc : f c <;> cases hd : f d <;> simp_all

/-- **Kochen–Specker theorem (18-vector version).**  The explicit 18-vector configuration in
`ℝ⁴` admits no `{0,1}`-coloring. -/
theorem kochen_specker_18 : ¬ ∃ f : Fin 18 → Bool, IsKSColoring f := by
  rintro ⟨f, hf⟩
  have c1 := ctx_sum_eq_one hf 0 1 2 3 (by decide)
  have c2 := ctx_sum_eq_one hf 0 4 5 6 (by decide)
  have c3 := ctx_sum_eq_one hf 7 8 2 9 (by decide)
  have c4 := ctx_sum_eq_one hf 7 10 6 11 (by decide)
  have c5 := ctx_sum_eq_one hf 1 4 12 13 (by decide)
  have c6 := ctx_sum_eq_one hf 8 10 13 14 (by decide)
  have c7 := ctx_sum_eq_one hf 15 16 3 9 (by decide)
  have c8 := ctx_sum_eq_one hf 15 17 5 11 (by decide)
  have c9 := ctx_sum_eq_one hf 16 17 12 14 (by decide)
  omega

end Phys

