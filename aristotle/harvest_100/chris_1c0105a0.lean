/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

variable {n : ℕ}

/-- The *centered indicator* of a vertex set `S` inside a vertex set of size `n`:
the indicator function of `S` minus its mean value `|S|/n`.  It is orthogonal to
the all-ones vector. -/
noncomputable def centeredIndicator (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  (if i ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / (n : ℝ)

/-- The centered indicator has zero total sum, i.e. it is orthogonal to the all-ones
vector. -/
lemma sum_centeredIndicator (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [centeredIndicator, Finset.sum_sub_distrib, Finset.card_univ]
  field_simp
  ring

/-- The squared euclidean norm of the centered indicator of `S` is `|S| - |S|²/n`. -/
lemma sum_sq_centeredIndicator (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsq : ∀ i : Fin n, centeredIndicator S i ^ 2
      = (if i ∈ S then (1 : ℝ) else 0)
        - 2 * (S.card : ℝ) / (n : ℝ) * (if i ∈ S then (1 : ℝ) else 0)
        + (S.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    intro i
    by_cases h : i ∈ S <;> simp [centeredIndicator, h] <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.card_univ]
  field_simp
  ring

/-- The squared euclidean norm of the centered indicator is at most `|S|`. -/
lemma sum_sq_centeredIndicator_le (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i ^ 2 ≤ (S.card : ℝ) := by
  rw [sum_sq_centeredIndicator hn S]
  have : 0 ≤ (S.card : ℝ) ^ 2 / (n : ℝ) := by positivity
  linarith

/-- **Key intermediate lemma.**  For a `d`-regular weighted graph (all row and column
sums of `A` equal `d`), the bilinear form of `A` applied to the centered indicators of
`S` and `T` is exactly the edge discrepancy `e(S,T) - d|S||T|/n`. -/
lemma bilinear_centeredIndicator (hn : 0 < n) (A : Fin n → Fin n → ℝ) (d : ℝ)
    (hrow : ∀ i, ∑ j, A i j = d) (hcol : ∀ j, ∑ i, A i j = d)
    (S T : Finset (Fin n)) :
    ∑ i, ∑ j, centeredIndicator S i * A i j * centeredIndicator T j
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set s : ℝ := (S.card : ℝ) / (n : ℝ) with hs
  set t : ℝ := (T.card : ℝ) / (n : ℝ) with ht
  -- expand the product
  have hexp : ∀ i j : Fin n,
      centeredIndicator S i * A i j * centeredIndicator T j
        = (if i ∈ S then (1:ℝ) else 0) * A i j * (if j ∈ T then (1:ℝ) else 0)
          - t * ((if i ∈ S then (1:ℝ) else 0) * A i j)
          - s * (A i j * (if j ∈ T then (1:ℝ) else 0))
          + s * t * A i j := by
    intro i j
    simp only [centeredIndicator, ← hs, ← ht]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hexp i j))]
  -- split the double sum into four pieces
  have hsplit : ∀ i : Fin n,
      ∑ j, ((if i ∈ S then (1:ℝ) else 0) * A i j * (if j ∈ T then (1:ℝ) else 0)
          - t * ((if i ∈ S then (1:ℝ) else 0) * A i j)
          - s * (A i j * (if j ∈ T then (1:ℝ) else 0))
          + s * t * A i j)
        = (∑ j, (if i ∈ S then (1:ℝ) else 0) * A i j * (if j ∈ T then (1:ℝ) else 0))
          - t * (∑ j, (if i ∈ S then (1:ℝ) else 0) * A i j)
          - s * (∑ j, A i j * (if j ∈ T then (1:ℝ) else 0))
          + s * t * (∑ j, A i j) := by
    intro i
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- evaluate each of the four sums
  have h1 : ∑ i, ∑ j, (if i ∈ S then (1:ℝ) else 0) * A i j * (if j ∈ T then (1:ℝ) else 0)
      = ∑ i ∈ S, ∑ j ∈ T, A i j := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (by intro x _ hx; simp [hx])]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.sum_subset (Finset.subset_univ T) (by intro x _ hx; simp [hx])]
    exact Finset.sum_congr rfl (fun j hj => by simp [hi, hj])
  have h2 : ∑ i, ∑ j, (if i ∈ S then (1:ℝ) else 0) * A i j = d * S.card := by
    have : ∀ i : Fin n, ∑ j, (if i ∈ S then (1:ℝ) else 0) * A i j
        = (if i ∈ S then (1:ℝ) else 0) * d := by
      intro i; rw [← Finset.mul_sum, hrow i]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.sum_mul]
    simp [mul_comm]
  have h3 : ∑ i, ∑ j, A i j * (if j ∈ T then (1:ℝ) else 0) = d * T.card := by
    rw [Finset.sum_comm]
    have : ∀ j : Fin n, ∑ i, A i j * (if j ∈ T then (1:ℝ) else 0)
        = d * (if j ∈ T then (1:ℝ) else 0) := by
      intro j; rw [← Finset.sum_mul, hcol j]
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum]
    simp
  have h4 : ∑ i, ∑ j, A i j = d * n := by
    rw [Finset.sum_congr rfl (fun i _ => hrow i)]
    simp [Finset.card_univ, mul_comm]
  rw [h1, h2, h3, h4, hs, ht]
  field_simp
  ring

/-- **Expander mixing lemma** (Alon–Chung, as in Hoory–Linial–Wigderson).

Let `A` be the (weighted) adjacency matrix of a `d`-regular graph on `n` vertices,
so that every row sum and every column sum of `A` equals `d`.  Suppose that the
bilinear form of `A` is bounded by `lam` on the orthogonal complement of the all-ones
vector, i.e. `|xᵀ A y| ≤ lam ‖x‖ ‖y‖` whenever `x` and `y` have zero coordinate sum
(for a symmetric `A` this holds with `lam` the second largest eigenvalue in absolute
value).  Then for all vertex sets `S`, `T` the number of edges between `S` and `T`
deviates from its "expected" value `d|S||T|/n` by at most `lam √(|S||T|)`. -/
theorem wigderson_expander_mixing {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (d lam : ℝ)
    (hrow : ∀ i, ∑ j, A i j = d)
    (hcol : ∀ j, ∑ i, A i j = d)
    (hlam : 0 ≤ lam)
    (hbil : ∀ x y : Fin n → ℝ, ∑ i, x i = 0 → ∑ i, y i = 0 →
      |∑ i, ∑ j, x i * A i j * y j|
        ≤ lam * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (S T : Finset (Fin n)) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (n : ℝ)|
      ≤ lam * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  have hkey := bilinear_centeredIndicator hn A d hrow hcol S T
  have hb := hbil (centeredIndicator S) (centeredIndicator T)
    (sum_centeredIndicator hn S) (sum_centeredIndicator hn T)
  rw [hkey] at hb
  refine hb.trans ?_
  have hS := sum_sq_centeredIndicator_le hn S
  have hT := sum_sq_centeredIndicator_le hn T
  have hS0 : (0 : ℝ) ≤ ∑ i, centeredIndicator S i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT0 : (0 : ℝ) ≤ ∑ i, centeredIndicator T i ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsS : Real.sqrt (∑ i, centeredIndicator S i ^ 2) ≤ Real.sqrt (S.card : ℝ) :=
    Real.sqrt_le_sqrt hS
  have hsT : Real.sqrt (∑ i, centeredIndicator T i ^ 2) ≤ Real.sqrt (T.card : ℝ) :=
    Real.sqrt_le_sqrt hT
  have hprod : Real.sqrt (∑ i, centeredIndicator S i ^ 2)
      * Real.sqrt (∑ i, centeredIndicator T i ^ 2)
      ≤ Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
    rw [Real.sqrt_mul (by positivity)]
    exact mul_le_mul hsS hsT (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc lam * Real.sqrt (∑ i, centeredIndicator S i ^ 2)
        * Real.sqrt (∑ i, centeredIndicator T i ^ 2)
      = lam * (Real.sqrt (∑ i, centeredIndicator S i ^ 2)
        * Real.sqrt (∑ i, centeredIndicator T i ^ 2)) := by ring
    _ ≤ lam * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod hlam

/-- Sanity check: the hypotheses of `wigderson_expander_mixing` are satisfiable by a
nonzero matrix.  The complete weighted graph `A ≡ 1` is `n`-regular and its bilinear
form vanishes on vectors of zero sum, so it satisfies the hypotheses with `lam = 0`. -/
example (n : ℕ) (hn : 0 < n) (S T : Finset (Fin n)) :
    |(∑ _i ∈ S, ∑ _j ∈ T, (1 : ℝ)) - (n : ℝ) * S.card * T.card / (n : ℝ)|
      ≤ 0 * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by
  refine wigderson_expander_mixing hn (fun _ _ => (1 : ℝ)) (n : ℝ) 0
    (by simp [Finset.card_univ]) (by simp [Finset.card_univ]) le_rfl ?_ S T
  intro x y hx hy
  have hxy : ∀ i : Fin n, ∑ j, x i * 1 * y j = x i * ∑ j, y j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => hxy i), hy]
  simp

end Frontier

