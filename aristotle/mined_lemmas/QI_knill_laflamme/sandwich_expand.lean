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

theorem sandwich_expand (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) (x y : ι → ℂ) :
    P * (∑ i, x i • E i)ᴴ * (∑ j, y j • E j) * P
      = ∑ i, ∑ j, ((starRingEnd ℂ) (x i) * y j) • (P * (E i)ᴴ * E j * P) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, smul_mul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

omit [DecidableEq ι] in
