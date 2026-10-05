import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/

theorem relEntropy_conj_diagonal (U : unitary (Matrix n n ℂ)) (p q : n → ℝ) :
    relEntropy ((U : Matrix n n ℂ) * diagonal (fun i => (p i : ℂ)) * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * diagonal (fun i => (q i : ℂ)) * star (U : Matrix n n ℂ))
      = klDiv p q := by
  have hU1 : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.2.1
  rw [relEntropy, matLog_conj_diagonal, matLog_conj_diagonal]
  have hprod : ((U : Matrix n n ℂ) * diagonal (fun i => (p i : ℂ)) * star (U : Matrix n n ℂ)) *
      ((U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        - (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * (diagonal (fun i => (p i : ℂ)) *
          (diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
            - diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ)))) * star (U : Matrix n n ℂ) := by
    have : ∀ X Y : Matrix n n ℂ,
        ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) *
          ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ))
          = (U : Matrix n n ℂ) * (X * Y) * star (U : Matrix n n ℂ) := by
      intro X Y
      calc ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)) *
          ((U : Matrix n n ℂ) * Y * star (U : Matrix n n ℂ))
          = (U : Matrix n n ℂ) * X * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ))
            * Y * star (U : Matrix n n ℂ) := by noncomm_ring
        _ = (U : Matrix n n ℂ) * (X * Y) * star (U : Matrix n n ℂ) := by
            rw [hU1]; noncomm_ring
    have hsub : (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        - (U : Matrix n n ℂ) * diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))
          * star (U : Matrix n n ℂ)
        = (U : Matrix n n ℂ) * (diagonal (fun i => ((Real.log (p i) : ℝ) : ℂ))
            - diagonal (fun i => ((Real.log (q i) : ℝ) : ℂ))) * star (U : Matrix n n ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [hsub, this]
  rw [hprod]
  rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
  have hdd : (diagonal fun i => (p i : ℂ)) *
      ((diagonal fun i => ((Real.log (p i) : ℝ) : ℂ))
        - diagonal fun i => ((Real.log (q i) : ℝ) : ℂ))
      = diagonal (fun i => (p i : ℂ) *
          (((Real.log (p i) : ℝ) : ℂ) - ((Real.log (q i) : ℝ) : ℂ))) := by
    rw [Matrix.mul_sub, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, mul_sub]
  rw [hdd, Matrix.trace_diagonal, klDiv]
  push_cast
  simp [Complex.re_sum]

end QI

import Mathlib

/-!
# Classical relative entropy and the classical data-processing inequality

This file develops the classical (commutative) part of the data-processing inequality:
the Kullback–Leibler divergence of two probability vectors does not increase when both
are pushed through a stochastic map.
-/

open scoped BigOperators

namespace QI

variable {ι κ : Type*}

/-- Kullback–Leibler divergence of two nonnegative vectors, with the usual conventions
`0 * log 0 = 0` (implemented through `Real.log 0 = 0`). -/
