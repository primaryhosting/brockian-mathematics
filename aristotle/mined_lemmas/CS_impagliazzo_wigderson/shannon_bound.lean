/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
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

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

lemma shannon_bound (n : ℕ) :
    (gateSet (n + (2 ^ (n / 100) - 1))).card ^ (2 ^ (n / 100) - 1) * (2 ^ (n / 100) - 1 + 1)
      < 2 ^ 2 ^ n := by
  set t := n / 100 with ht
  set s := 2 ^ t - 1 with hs
  set N := n + s with hN
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hs1 : s + 1 = 2 ^ t := by omega
  rcases lt_or_ge n 100 with hn | hn
  · -- then `t = 0` and there is a single circuit code
    have ht0 : t = 0 := by omega
    have hs0 : s = 0 := by simp [hs, ht0]
    have h2 : 2 ≤ 2 ^ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    simp only [hs0, pow_zero, one_mul]
    omega
  · -- the main case
    have hbase : (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := card_gateSet_le N
    have hpoly := two_n_le_two_pow hn
    have hts : t ≤ n / 4 := by omega
    have hsle : s ≤ 2 ^ (n / 4) := by
      have : 2 ^ t ≤ 2 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) hts
      omega
    have hnle : n ≤ 2 ^ (n / 4) := by omega
    have hNle : N ≤ 2 ^ (n / 4 + 1) := by
      have : 2 ^ (n / 4 + 1) = 2 ^ (n / 4) + 2 ^ (n / 4) := by ring
      omega
    have hN1 : 1 ≤ N := by omega
    -- bound the number of gates by a power of two
    have hgate : (gateSet N).card ≤ 2 ^ (2 * (n / 4) + 5) := by
      have h5 : 2 + N + 2 * N ^ 2 ≤ 8 * N ^ 2 := by nlinarith
      have h6 : N ^ 2 ≤ (2 ^ (n / 4 + 1)) ^ 2 := Nat.pow_le_pow_left hNle 2
      have h7 : (8 : ℕ) * (2 ^ (n / 4 + 1)) ^ 2 = 2 ^ (2 * (n / 4) + 5) := by
        rw [← pow_mul]
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        ring_nf
      calc (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := hbase
        _ ≤ 8 * N ^ 2 := h5
        _ ≤ 8 * (2 ^ (n / 4 + 1)) ^ 2 := by exact Nat.mul_le_mul_left 8 h6
        _ = 2 ^ (2 * (n / 4) + 5) := h7
    -- the exponent of the total count is small
    have hexp : (2 * (n / 4) + 5) * s + t < 2 ^ n := by
      have h1 : 2 * (n / 4) + 5 ≤ 2 ^ (n / 4) := by omega
      have h2 : (2 * (n / 4) + 5) * s ≤ 2 ^ (n / 4) * 2 ^ (n / 4) :=
        Nat.mul_le_mul h1 hsle
      have h3 : 2 ^ (n / 4) * 2 ^ (n / 4) = 2 ^ (2 * (n / 4)) := by
        rw [← pow_add]; ring_nf
      have h4 : t ≤ 2 ^ (n / 4) := le_trans (by omega) hnle
      have h5 : 2 ^ (n / 4) ≤ 2 ^ (2 * (n / 4)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : 2 ^ (2 * (n / 4)) + 2 ^ (2 * (n / 4)) = 2 ^ (2 * (n / 4) + 1) := by ring
      have h7 : 2 ^ (2 * (n / 4) + 1) ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h8 : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    calc (gateSet N).card ^ s * (s + 1)
        ≤ (2 ^ (2 * (n / 4) + 5)) ^ s * 2 ^ t := by
          rw [hs1]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgate s)
      _ = 2 ^ ((2 * (n / 4) + 5) * s + t) := by rw [← pow_mul, ← pow_add]
      _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hexp

/-- **Shannon's theorem.**  There exist Boolean functions of exponential circuit complexity. -/
