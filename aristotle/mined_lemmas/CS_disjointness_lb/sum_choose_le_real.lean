import Mathlib
import RequestProject.DisjointnessLb

/-!
# Deterministic two-way communication complexity of set disjointness

As a companion to `CS.disjointness_lb` (a linear lower bound for *randomized* one-way
protocols), this file formalises the general *two-way deterministic* model as protocol
trees and proves the classical fooling-set lower bound: any deterministic protocol
computing set disjointness on an `n`-element universe has cost at least `n`.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- Bitwise complement of a characteristic vector. -/

lemma sum_choose_le_real (n k : ℕ) (hk : k ≤ n) :
    ((∑ j ∈ range (k + 1), n.choose j : ℕ) : ℝ) ≤ 8 ^ k * (8 / 7) ^ (n - k) := by
  have hmono : ∀ j ∈ range (k + 1),
      ((1 : ℝ) / 8) ^ k * (7 / 8) ^ (n - k) ≤ (1 / 8) ^ j * (7 / 8) ^ (n - j) := by
    intro j hj
    simp only [mem_range, Nat.lt_succ_iff] at hj
    obtain ⟨s, rfl⟩ : ∃ s, k = j + s := ⟨k - j, by omega⟩
    have h1 : n - j = (n - (j + s)) + s := by omega
    rw [h1, pow_add, pow_add]
    have h2 : ((1 : ℝ) / 8) ^ s ≤ (7 / 8) ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num) s
    have h3 : (1 / 8 : ℝ) ^ j * (1 / 8) ^ s * (7 / 8) ^ (n - (j + s))
        = ((1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - (j + s))) * (1 / 8) ^ s := by ring
    have h4 : (1 / 8 : ℝ) ^ j * ((7 / 8) ^ (n - (j + s)) * (7 / 8) ^ s)
        = ((1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - (j + s))) * (7 / 8) ^ s := by ring
    rw [h3, h4]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hw : (0 : ℝ) < (1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k) := by positivity
  have step1 : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k))
      ≤ ∑ j ∈ range (k + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hmono j hj) (by positivity)
  have step2 : (∑ j ∈ range (k + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)))
      ≤ ∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun i _ _ => by positivity)
    simp only [mem_range] at *
    omega
  have step3 : (∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j))) = 1 := by
    have h5 : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * ((1 / 8) ^ j * (7 / 8) ^ (n - j))
        = ∑ j ∈ range (n + 1), (1 / 8 : ℝ) ^ j * (7 / 8) ^ (n - j) * (n.choose j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h5, ← add_pow]
    norm_num
  have hle : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k)) ≤ 1 := by
    linarith
  have hinv : (8 : ℝ) ^ k * (8 / 7) ^ (n - k) = ((1 / 8 : ℝ) ^ k * (7 / 8) ^ (n - k))⁻¹ := by
    rw [mul_inv, ← inv_pow, ← inv_pow]
    norm_num
  rw [hinv, inv_eq_one_div, le_div_iff₀ hw]
  push_cast
  exact hle

/-- Counting step: the inputs whose "reconstruction" from Alice's message is within
Hamming distance `n / 8` are determined by the message together with a small
difference set, so there are at most `2 ^ c * ∑_{j ≤ n/8} C(n,j)` of them. -/
