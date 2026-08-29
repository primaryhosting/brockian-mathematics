/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- because Lean 4 requires all `import` commands to precede any command, including a module
-- docstring. The identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (f i - g j)`. -/
noncomputable def cosKernel {n : ℕ} (f g : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (f i - g j)

/-- Absolute-value form of the Cauchy–Schwarz inequality for finite real sums,
obtained from `Real.sum_mul_le_sqrt_mul_sqrt`. -/
lemma abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  refine abs_le.2 ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt s f g⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  simp only [neg_mul, Finset.sum_neg_distrib, even_two.neg_pow] at h
  linarith

/-- Splitting the cosine kernel: the bilinear form of `cosKernel f g` decomposes as a
sum of two rank-one terms. -/
lemma bilin_cosKernel_eq {n : ℕ} (f g u v : Fin n → ℝ) :
    ∑ i, ∑ j, u i * Real.cos (f i - g j) * v j =
      (∑ i, u i * Real.cos (f i)) * (∑ j, v j * Real.cos (g j)) +
      (∑ i, u i * Real.sin (f i)) * (∑ j, v j * Real.sin (g j)) := by
  have h : ∀ i j : Fin n, u i * Real.cos (f i - g j) * v j =
      (u i * Real.cos (f i)) * (v j * Real.cos (g j)) +
      (u i * Real.sin (f i)) * (v j * Real.sin (g j)) := by
    intro i j
    rw [Real.cos_sub]; ring
  calc ∑ i, ∑ j, u i * Real.cos (f i - g j) * v j
      = ∑ i, ∑ j, ((u i * Real.cos (f i)) * (v j * Real.cos (g j)) +
          (u i * Real.sin (f i)) * (v j * Real.sin (g j))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j
    _ = _ := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Pythagorean identity in sum form. -/
lemma sum_cos_sq_add_sum_sin_sq {n : ℕ} (f : Fin n → ℝ) :
    (∑ i, Real.cos (f i) ^ 2) + (∑ i, Real.sin (f i) ^ 2) = (n : ℝ) := by
  rw [← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

/-- **Trace-norm (nuclear norm) bound for the cosine kernel.**

For all real phases `f, g : Fin n → ℝ`, the matrix `C i j = cos (f i - g j)` has bilinear form
bounded by `n ‖u‖ ‖v‖`; equivalently, the operator norm of `C` is at most `n`.  The proof
splits `C` into the two rank-one pieces coming from `cos (a - b) = cos a cos b + sin a sin b`
and bounds the sum of their nuclear norms, `‖cos f‖‖cos g‖ + ‖sin f‖‖sin g‖`, by `n`. -/
theorem CosTraceNorm1597 {n : ℕ} (f g u v : Fin n → ℝ) :
    |∑ i, ∑ j, u i * cosKernel f g i j * v j| ≤
      (n : ℝ) * Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  classical
  set U := Real.sqrt (∑ i, u i ^ 2) with hU
  set V := Real.sqrt (∑ i, v i ^ 2) with hV
  set p := Real.sqrt (∑ i, Real.cos (f i) ^ 2) with hp
  set q := Real.sqrt (∑ i, Real.sin (f i) ^ 2) with hq
  set r := Real.sqrt (∑ i, Real.cos (g i) ^ 2) with hr
  set s := Real.sqrt (∑ i, Real.sin (g i) ^ 2) with hs
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the four Cauchy–Schwarz bounds
  have h1 : |∑ i, u i * Real.cos (f i)| ≤ U * p :=
    abs_sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 : |∑ j, v j * Real.cos (g j)| ≤ V * r :=
    abs_sum_mul_le_sqrt_mul_sqrt _ _ _
  have h3 : |∑ i, u i * Real.sin (f i)| ≤ U * q :=
    abs_sum_mul_le_sqrt_mul_sqrt _ _ _
  have h4 : |∑ j, v j * Real.sin (g j)| ≤ V * s :=
    abs_sum_mul_le_sqrt_mul_sqrt _ _ _
  -- the Pythagorean constraints
  have hpq : p ^ 2 + q ^ 2 = (n : ℝ) := by
    have hc : (0:ℝ) ≤ ∑ i, Real.cos (f i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsn : (0:ℝ) ≤ ∑ i, Real.sin (f i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hp, hq, Real.sq_sqrt hc, Real.sq_sqrt hsn]
    exact sum_cos_sq_add_sum_sin_sq f
  have hrs : r ^ 2 + s ^ 2 = (n : ℝ) := by
    have hc : (0:ℝ) ≤ ∑ i, Real.cos (g i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsn : (0:ℝ) ≤ ∑ i, Real.sin (g i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hr, hs, Real.sq_sqrt hc, Real.sq_sqrt hsn]
    exact sum_cos_sq_add_sum_sin_sq g
  -- two-dimensional Cauchy–Schwarz / AM-GM
  have hcs : p * r + q * s ≤ (n : ℝ) := by
    nlinarith [sq_nonneg (p - r), sq_nonneg (q - s)]
  have hkey : |∑ i, ∑ j, u i * cosKernel f g i j * v j| ≤ U * V * (p * r + q * s) := by
    have hdecomp : ∑ i, ∑ j, u i * cosKernel f g i j * v j =
        (∑ i, u i * Real.cos (f i)) * (∑ j, v j * Real.cos (g j)) +
        (∑ i, u i * Real.sin (f i)) * (∑ j, v j * Real.sin (g j)) :=
      bilin_cosKernel_eq f g u v
    rw [hdecomp]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hb1 : |∑ i, u i * Real.cos (f i)| * |∑ j, v j * Real.cos (g j)| ≤ (U * p) * (V * r) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hb2 : |∑ i, u i * Real.sin (f i)| * |∑ j, v j * Real.sin (g j)| ≤ (U * q) * (V * s) :=
      mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
    nlinarith [hb1, hb2]
  have : U * V * (p * r + q * s) ≤ U * V * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  calc |∑ i, ∑ j, u i * cosKernel f g i j * v j| ≤ U * V * (p * r + q * s) := hkey
    _ ≤ U * V * (n : ℝ) := this
    _ = (n : ℝ) * U * V := by ring

/-- Companion bound: the trace of the cosine kernel is bounded by `n` in absolute value. -/
theorem abs_trace_cosKernel_le {n : ℕ} (f g : Fin n → ℝ) :
    |(cosKernel f g).trace| ≤ (n : ℝ) := by
  classical
  have h : (cosKernel f g).trace = ∑ i, Real.cos (f i - g i) := rfl
  rw [h]
  calc |∑ i, Real.cos (f i - g i)| ≤ ∑ i : Fin n, |Real.cos (f i - g i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

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

