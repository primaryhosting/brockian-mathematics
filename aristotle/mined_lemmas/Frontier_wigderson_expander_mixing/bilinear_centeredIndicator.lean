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
