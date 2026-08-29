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

theorem sum_ip_unitary {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (g : ι → n → ℂ) :
    ∑ a, ip (∑ i, U i a • g i) (∑ i, U i a • g i) = ∑ i, ip (g i) (g i) := by
  simp only [ip_self_trace, ← Matrix.trace_sum, sum_outer_unitary hU]

omit [DecidableEq ι] in
