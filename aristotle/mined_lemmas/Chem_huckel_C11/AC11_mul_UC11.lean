/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`, so the
-- required header appears above as an ordinary block comment with identical text.)

import Mathlib

/-!
# Huckel C 11

The adjacency eigenvalues of the cycle graph `C₁₁` are `2·cos(2πk/11)` for `k = 0, …, 10`.

The proof diagonalizes the adjacency matrix `A` of `SimpleGraph.cycleGraph 11` by the
discrete Fourier (Vandermonde) matrix `U j k = ω^{jk}`, where `ω = exp(2πi/11)`:
`A * U = U * diagonal d` with `d k = ω^k + ω^{-k} = 2 cos (2πk/11)`.
Since `det U ≠ 0` (`Matrix.det_vandermonde_ne_zero_iff`, `ω` being a primitive root),
`det (A - z) = ∏ k (d k - z)`, and `Matrix.exists_mulVec_eq_zero_iff` converts this into
the statement about eigenvalues.
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 11-th root of unity. -/

theorem AC11_mul_UC11 : AC11 * UC11 = UC11 * Matrix.diagonal dC11 := by
  have hadj : ∀ j l : Fin 11, (cycleGraph 11).Adj j l ↔ (l = j + 10 ∨ l = j + 1) := by decide
  ext j k
  set z : ℂ := om ^ (k : ℕ) with hzdef
  have hz11 : z ^ 11 = 1 := by
    rw [hzdef, ← pow_mul, mul_comm, pow_mul, om_pow_eleven, one_pow]
  have hUentry : ∀ l : Fin 11, UC11 l k = z ^ (l : ℕ) := by
    intro l
    rw [UC11, Matrix.vandermonde_apply, hzdef, ← pow_mul, mul_comm, pow_mul]
  -- the right-hand side
  rw [Matrix.mul_diagonal, hUentry j, dC11, ← hzdef]
  have hz10 : om ^ (10 * (k : ℕ)) = z ^ 10 := by
    rw [hzdef, ← pow_mul, mul_comm]
  rw [hz10]
  -- the left-hand side
  rw [Matrix.mul_apply]
  have hstep : ∀ l : Fin 11, AC11 j l * UC11 l k
      = (if l = j + 10 then z ^ (l : ℕ) else 0) + (if l = j + 1 then z ^ (l : ℕ) else 0) := by
    intro l
    rw [AC11, SimpleGraph.adjMatrix_apply, hUentry l]
    by_cases h1 : l = j + 10 <;> by_cases h2 : l = j + 1 <;>
      simp [hadj j l, h1, h2] <;> simp_all
  rw [Finset.sum_congr rfl (fun l _ => hstep l), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e10 : ((j + 10 : Fin 11) : ℕ) = ((j : ℕ) + 10) % 11 := by simp [Fin.add_def]
  have e1 : ((j + 1 : Fin 11) : ℕ) = ((j : ℕ) + 1) % 11 := by simp [Fin.add_def]
  rw [e10, e1]
  have hmod : ∀ m : ℕ, z ^ (m % 11) = z ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m 11]
    rw [pow_add, pow_mul, hz11, one_pow, one_mul]
  rw [hmod, hmod, pow_add, pow_add, pow_one]
  ring

