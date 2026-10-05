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

private lemma arith_contradiction (n c k V g : ℕ) (hcon : 3 * (c + 1) < n) (hk : 8 * k ≤ n)
    (hkn : k ≤ n) (hG2 : 2 ^ n < 2 * g) (hGT : g ≤ 2 ^ c * V)
    (hV : (V : ℝ) ≤ 8 ^ k * (8 / 7) ^ (n - k)) : False := by
  have hVR : (0 : ℝ) ≤ V := by positivity
  have h1 : (2 : ℝ) ^ n < 2 * (2 ^ c * V) := by
    have h : ((2 ^ n : ℕ) : ℝ) < ((2 * (2 ^ c * V) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hG2 (by omega)
    push_cast at h
    exact h
  have h2 : ((8 : ℝ) / 7) ^ (n - k) ≤ (8 / 7) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ n < 2 ^ (c + 1) * 8 ^ k * (8 / 7) ^ n := by
    have e : (2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n = 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ n)) := by
      rw [pow_succ]; ring
    calc (2 : ℝ) ^ n < 2 * (2 ^ c * V) := h1
      _ ≤ 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ (n - k))) := by gcongr
      _ ≤ 2 * (2 ^ c * (8 ^ k * (8 / 7) ^ n)) := by gcongr
      _ = 2 ^ (c + 1) * 8 ^ k * (8 / 7) ^ n := e.symm
  have h24 : ((2 : ℝ) ^ n) ^ 24 < ((2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n) ^ 24 :=
    pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
  have a1 : ((2 : ℝ) ^ (c + 1)) ^ 24 ≤ 2 ^ (8 * n) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have a2 : ((8 : ℝ) ^ k) ^ 24 ≤ 2 ^ (9 * n) := by
    have e : ((8 : ℝ) ^ k) ^ 24 = 2 ^ (72 * k) := by
      rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul]
      ring_nf
    rw [e]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have a3 : (((8 : ℝ) / 7) ^ n) ^ 24 ≤ 2 ^ (7 * n) := by
    rw [← pow_mul, mul_comm n 24, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) n
  have hfin : ((2 : ℝ) ^ (c + 1) * 8 ^ k * (8 / 7) ^ n) ^ 24 ≤ 2 ^ (8 * n) * 2 ^ (9 * n) * 2 ^ (7 * n) := by
    rw [mul_pow, mul_pow]
    gcongr
  have hL : ((2 : ℝ) ^ n) ^ 24 = 2 ^ (8 * n) * 2 ^ (9 * n) * 2 ^ (7 * n) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    ring_nf
  linarith

/-- **Set disjointness has linear randomized communication complexity.**

Model: a public-coin randomized one-way protocol on inputs `a b : Fin n → Bool`
(characteristic vectors of subsets of an `n`-element universe).  The public random
string is uniform on `Fin N` (`N > 0`); given the random string `r`, Alice sends the
`c`-bit message `msg r a : Fin (2 ^ c)` and Bob answers `out r (msg r a) b`.  The
protocol is assumed to err with probability at most `1/16` on every input pair.

Conclusion: `n ≤ 3 * (c + 1)`, i.e. the number `c` of communicated bits is `Ω(n)`. -/
