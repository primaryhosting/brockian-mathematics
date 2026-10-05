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

theorem exists_unit_smul {v : n → ℂ} (hv : v ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ip (r • v) (r • v) = 1 := by
  have hs0 : 0 < (ip v v).re := by
    rcases lt_or_eq_of_le (ip_self_nonneg v) with h | h
    · exact h
    · exact absurd (ip_self_eq_zero (by rw [← ip_self_re v, ← h]; simp)) hv
  refine ⟨((1 / Real.sqrt (ip v v).re : ℝ) : ℂ), ?_, ?_⟩
  · simp only [ne_eq, Complex.ofReal_eq_zero, one_div, inv_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 hs0)
  · rw [ip_smul_left, ip_smul_right, ← ip_self_re v]
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    norm_cast
    field_simp
    rw [Real.sq_sqrt hs0.le]

omit [DecidableEq n] in
