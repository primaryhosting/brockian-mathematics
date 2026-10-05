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

theorem mul_mixed_mulVec {A : Matrix n n ℂ} {E F : ι → Matrix n n ℂ} {U : Matrix ι ι ℂ}
    (hF : ∀ a, F a = ∑ i, U i a • E i) (v : n → ℂ) (a : ι) :
    (A * F a) *ᵥ v = ∑ i, U i a • ((A * E i) *ᵥ v) := by
  rw [hF a, Finset.mul_sum]
  simp [Matrix.sum_mulVec, smul_mulVec]

/-- Mixing the error operators by a unitary matrix does not change correctability. -/
