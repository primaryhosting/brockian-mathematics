/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem eq_smul_of_sum_outer {κ : Type} [Fintype κ] {u : κ → n → ℂ} {v : n → ℂ}
    {C : ℂ} (hv : ip v v = 1) (h : ∑ k, outer (u k) = C • outer v) (k : κ) :
    u k = (ip v (u k)) • v := by
  set c := ip v (u k) with hc
  set w := u k - c • v with hw
  have hvw : ip v w = 0 := by
    rw [hw, ip_sub_right, ip_smul_right, hv, mul_one, ← hc, sub_self]
  have hq := congrArg (fun M : Matrix n n ℂ => ip w (M *ᵥ w)) h
  simp only [Matrix.sum_mulVec, smul_mulVec, outer_mulVec,
    ip_sum_right, ip_smul_right, hvw, zero_mul, mul_zero] at hq
  have hall : ∀ k', ip (u k') w = 0 := by
    intro k'
    refine eq_zero_of_sum_mul_conj_eq_zero (z := fun k' => ip (u k') w) ?_ k'
    rw [← hq]
    exact Finset.sum_congr rfl fun k' _ => by rw [ip_conj]
  have hww : ip w w = 0 := by
    rw [hw, ip_sub_left, ip_smul_left, hvw, mul_zero, sub_zero]
    exact hall k
  have := ip_self_eq_zero hww
  rw [hw] at this
  have : u k - c • v = 0 := this
  linear_combination (norm := module) this

omit [DecidableEq n] in
