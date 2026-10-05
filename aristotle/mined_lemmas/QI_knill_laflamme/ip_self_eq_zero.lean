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

theorem ip_self_eq_zero {v : n → ℂ} (h : ip v v = 0) : v = 0 := by
  rw [ip_self_eq] at h
  have h' : (∑ i, Complex.normSq (v i)) = 0 := by exact_mod_cast h
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (v i))).1 h'
  funext i
  simpa using Complex.normSq_eq_zero.1 (this i (Finset.mem_univ i))

omit [DecidableEq n] in
