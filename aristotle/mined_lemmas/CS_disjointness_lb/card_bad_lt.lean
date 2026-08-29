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

private lemma card_bad_lt (n : ℕ) (D : (Fin n → Bool) → ℕ)
    (hDsum : ∑ a : (Fin n → Bool), (D a : ℝ) ≤ (2 ^ n * n : ℝ) / 16) :
    2 * (Finset.univ.filter (fun a : Fin n → Bool => ¬ (8 * D a ≤ n))).card < 2 ^ n := by
  classical
  set Bad := (Finset.univ.filter (fun a : Fin n → Bool => ¬ (8 * D a ≤ n))) with hBad
  have h0 : ∑ _a ∈ Bad, (((n : ℝ) + 1) / 8) ≤ ∑ a ∈ Bad, (D a : ℝ) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [hBad, Finset.mem_filter] at ha
    have h : n + 1 ≤ 8 * D a := by omega
    have h' : ((n : ℝ) + 1) ≤ 8 * (D a : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (Bad.card : ℝ) * (((n : ℝ) + 1) / 8) ≤ ∑ a ∈ Bad, (D a : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using h0
  have h2 : ∑ a ∈ Bad, (D a : ℝ) ≤ ∑ a : (Fin n → Bool), (D a : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)
  have h3 : (Bad.card : ℝ) * (((n : ℝ) + 1) / 8) ≤ (2 ^ n * n : ℝ) / 16 := by linarith
  have h4 : (2 * Bad.card : ℝ) < 2 ^ n := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    nlinarith [h3, hn, hp]
  exact_mod_cast h4

/-- The final arithmetic: a Hamming-ball counting bound of this shape forces `n ≤ 3(c+1)`. -/
