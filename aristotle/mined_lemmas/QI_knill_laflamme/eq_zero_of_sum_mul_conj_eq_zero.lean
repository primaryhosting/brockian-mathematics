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

theorem eq_zero_of_sum_mul_conj_eq_zero {κ : Type} [Fintype κ] {z : κ → ℂ}
    (h : ∑ k, z k * (starRingEnd ℂ) (z k) = 0) (k : κ) : z k = 0 := by
  have h2 : ((∑ k, Complex.normSq (z k) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (z k)).symm
  have h3 : (∑ k, Complex.normSq (z k)) = 0 := by exact_mod_cast h2
  have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg (z k)).1 h3
  exact Complex.normSq_eq_zero.1 (this k (Finset.mem_univ k))

omit [DecidableEq n] in
/-- If a sum of rank-one positive operators `outer (u m)` is proportional to `outer v`
with `v` a unit vector, then every `u m` is a multiple of `v`. -/
