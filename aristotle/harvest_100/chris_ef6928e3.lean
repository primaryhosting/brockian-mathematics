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

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Brockian

/-- The set of admissible bounds for the nuclear (trace) norm of a real matrix `A`:
`c` belongs to it iff `A` can be written as a finite sum of rank-one matrices
`u i ⊗ v i` whose total "product of Euclidean norms" is at most `c`. -/
def nuclearBounds {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Set ℝ :=
  {c : ℝ | ∃ (r : ℕ) (u : Fin r → Fin n → ℝ) (v : Fin r → Fin m → ℝ),
      (∀ j k, A j k = ∑ i, u i j * v i k) ∧
      ∑ i, Real.sqrt (∑ j, (u i j) ^ 2) * Real.sqrt (∑ k, (v i k) ^ 2) ≤ c}

/-- The nuclear norm (= trace norm = sum of the singular values) of a real matrix,
defined variationally as the infimum of the total rank-one mass of a decomposition. -/
noncomputable def nuclearNorm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  sInf (nuclearBounds A)

lemma nuclearBounds_nonempty {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    (nuclearBounds A).Nonempty := by
  classical
  refine ⟨∑ i : Fin n, Real.sqrt (∑ j : Fin n, (if j = i then (1 : ℝ) else 0) ^ 2) *
      Real.sqrt (∑ k, (A i k) ^ 2), n, fun i j => if j = i then (1 : ℝ) else 0,
      fun i k => A i k, ?_, le_rfl⟩
  intro j k
  simp

lemma nuclearBounds_bddBelow {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    BddBelow (nuclearBounds A) := by
  refine ⟨0, ?_⟩
  rintro c ⟨r, u, v, -, hc⟩
  refine le_trans ?_ hc
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Any admissible decomposition bounds the nuclear norm from above. -/
lemma nuclearNorm_le {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) {c : ℝ}
    (hc : c ∈ nuclearBounds A) : nuclearNorm A ≤ c :=
  csInf_le (nuclearBounds_bddBelow A) hc

lemma nuclearNorm_nonneg {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ nuclearNorm A := by
  refine le_csInf (nuclearBounds_nonempty A) ?_
  rintro c ⟨r, u, v, -, hc⟩
  refine le_trans ?_ hc
  exact Finset.sum_nonneg fun i _ => by positivity

/-- Discrete Cauchy–Schwarz in the form used below. -/
lemma sum_mul_le_sqrt_mul_sqrt {n : ℕ} (f g : Fin n → ℝ) :
    ∑ j, f j * g j ≤ Real.sqrt (∑ j, (f j) ^ 2) * Real.sqrt (∑ j, (g j) ^ 2) := by
  have h1 : (∑ j, f j * g j) ^ 2 ≤ (∑ j, (f j) ^ 2) * (∑ j, (g j) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by positivity)] at h2
  exact le_trans (le_abs_self _) h2

/-- The trace of a square matrix is a lower bound for its nuclear norm. -/
lemma trace_le_nuclearNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.trace ≤ nuclearNorm A := by
  refine le_csInf (nuclearBounds_nonempty A) ?_
  rintro c ⟨r, u, v, hA, hc⟩
  refine le_trans ?_ hc
  have htr : A.trace = ∑ i : Fin r, ∑ j : Fin n, u i j * v i j := by
    rw [Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hA j j
  rw [htr]
  exact Finset.sum_le_sum fun i _ => sum_mul_le_sqrt_mul_sqrt (u i) (v i)

/-- Key two-term Cauchy–Schwarz estimate behind the cosine bound. -/
lemma cs_two (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * c + b * d ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
  have h : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by nlinarith [sq_nonneg (a*d - b*c)]
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- **Cos Trace Norm 2003.**
For arbitrary real phases `x : Fin n → ℝ` and `y : Fin m → ℝ`, the `n × m` cosine matrix
`A j k = cos (x j - y k)` has nuclear (trace) norm at most `√(n·m)`. -/
theorem CosTraceNorm2003 (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    nuclearNorm (Matrix.of fun (j : Fin n) (k : Fin m) => Real.cos (x j - y k)) ≤
      Real.sqrt (n * m) := by
  set a : ℝ := Real.sqrt (∑ j, (Real.cos (x j)) ^ 2) with ha
  set b : ℝ := Real.sqrt (∑ j, (Real.sin (x j)) ^ 2) with hb
  set c : ℝ := Real.sqrt (∑ k, (Real.cos (y k)) ^ 2) with hcc
  set d : ℝ := Real.sqrt (∑ k, (Real.sin (y k)) ^ 2) with hd
  have key : a * c + b * d ≤ Real.sqrt (n * m) := by
    have hab : a ^ 2 + b ^ 2 = (n : ℝ) := by
      rw [ha, hb, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      simp [Real.cos_sq_add_sin_sq]
    have hcd : c ^ 2 + d ^ 2 = (m : ℝ) := by
      rw [hcc, hd, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      simp [Real.cos_sq_add_sin_sq]
    have := cs_two a b c d (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    rwa [hab, hcd] at this
  refine nuclearNorm_le _ ⟨2, ![fun j => Real.cos (x j), fun j => Real.sin (x j)],
    ![fun k => Real.cos (y k), fun k => Real.sin (y k)], ?_, ?_⟩
  · intro j k
    simp [Fin.sum_univ_two, Real.cos_sub]
  · simpa [Fin.sum_univ_two, ha, hb, hcc, hd] using key

/-- **Weighted Cos Trace Norm bound** (generalisation of `CosTraceNorm2003`).
For weights `a : Fin n → ℝ`, `b : Fin m → ℝ` and phases `x`, `y`, the matrix
`A j k = a j * b k * cos (x j - y k)` has trace norm at most `‖a‖₂ * ‖b‖₂`. -/
theorem CosTraceNorm2003_weighted (n m : ℕ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    nuclearNorm (Matrix.of fun (j : Fin n) (k : Fin m) => a j * b k * Real.cos (x j - y k)) ≤
      Real.sqrt (∑ j, (a j) ^ 2) * Real.sqrt (∑ k, (b k) ^ 2) := by
  set p : ℝ := Real.sqrt (∑ j, (a j * Real.cos (x j)) ^ 2) with hp
  set q : ℝ := Real.sqrt (∑ j, (a j * Real.sin (x j)) ^ 2) with hq
  set s : ℝ := Real.sqrt (∑ k, (b k * Real.cos (y k)) ^ 2) with hs
  set t : ℝ := Real.sqrt (∑ k, (b k * Real.sin (y k)) ^ 2) with ht
  have key : p * s + q * t ≤ Real.sqrt (∑ j, (a j) ^ 2) * Real.sqrt (∑ k, (b k) ^ 2) := by
    have hpq : p ^ 2 + q ^ 2 = ∑ j, (a j) ^ 2 := by
      rw [hp, hq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := Real.sin_sq_add_cos_sq (x j)
      nlinarith [this]
    have hst : s ^ 2 + t ^ 2 = ∑ k, (b k) ^ 2 := by
      rw [hs, ht, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := Real.sin_sq_add_cos_sq (y k)
      nlinarith [this]
    have h := cs_two p q s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    rw [hpq, hst] at h
    rwa [Real.sqrt_mul (by positivity)] at h
  refine nuclearNorm_le _
    ⟨2, ![fun j => a j * Real.cos (x j), fun j => a j * Real.sin (x j)],
      ![fun k => b k * Real.cos (y k), fun k => b k * Real.sin (y k)], ?_, ?_⟩
  · intro j k
    simp only [Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_sub]
    ring
  · simpa [Fin.sum_univ_two, hp, hq, hs, ht] using key

/-- Trace-norm bound for the "sum" cosine kernel `A j k = cos (x j + y k)`. -/
theorem CosTraceNorm2003_add (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    nuclearNorm (Matrix.of fun (j : Fin n) (k : Fin m) => Real.cos (x j + y k)) ≤
      Real.sqrt (n * m) := by
  have h := CosTraceNorm2003 n m x (fun k => -y k)
  simpa [sub_neg_eq_add] using h

/-- Sharpness of `CosTraceNorm2003`: for the square Gram-type cosine matrix
`A j k = cos (x j - x k)` the bound `√(n·n) = n` is attained. -/
theorem CosTraceNorm2003_sharp (n : ℕ) (x : Fin n → ℝ) :
    nuclearNorm (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k)) = (n : ℝ) := by
  refine le_antisymm ?_ ?_
  · have h := CosTraceNorm2003 n n x x
    rwa [show ((n : ℝ) * n) = (n : ℝ) ^ 2 by ring, Real.sqrt_sq (Nat.cast_nonneg n)] at h
  · have h := trace_le_nuclearNorm (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k))
    have htr : (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k)).trace = (n : ℝ) := by
      simp [Matrix.trace, Matrix.diag]
    rwa [htr] at h

end Brockian

