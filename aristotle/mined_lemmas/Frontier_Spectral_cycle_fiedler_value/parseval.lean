/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma parseval [NeZero N] (x : ZMod N → ℂ) :
    ∑ k : ZMod N, normSq (∑ j : ZMod N, x j * chi N (j * k))
      = N * ∑ j : ZMod N, normSq (x j) := by
  have key : ∀ k : ZMod N,
      ((normSq (∑ j : ZMod N, x j * chi N (j * k)) : ℝ) : ℂ)
        = ∑ j : ZMod N, ∑ l : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k) := by
    intro k
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, chi_conj]
    have h : chi N (j * k) * chi N (-(l * k)) = chi N ((j - l) * k) := by
      rw [← chi_add]; congr 1; ring
    calc x j * chi N (j * k) * (conj (x l) * chi N (-(l * k)))
        = (x j * conj (x l)) * (chi N (j * k) * chi N (-(l * k))) := by ring
      _ = _ := by rw [h]
  have main : ((∑ k : ZMod N, normSq (∑ j : ZMod N, x j * chi N (j * k)) : ℝ) : ℂ)
      = ((N * ∑ j : ZMod N, normSq (x j) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [key]
    have h3 : ∑ k : ZMod N, ∑ j : ZMod N, ∑ l : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k)
        = ∑ j : ZMod N, ∑ l : ZMod N, ∑ k : ZMod N,
            (x j * conj (x l)) * chi N ((j - l) * k) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm ..
    rw [h3]
    have h2 : ∀ j l : ZMod N, ∑ k : ZMod N, (x j * conj (x l)) * chi N ((j - l) * k)
        = (x j * conj (x l)) * (if j - l = 0 then (N : ℂ) else 0) := by
      intro j l; rw [← Finset.mul_sum, sum_chi]
    simp only [h2, sub_eq_zero]
    simp [Finset.sum_ite_eq, Complex.mul_conj, Finset.mul_sum, mul_comm]
  exact_mod_cast main

/-- The Fourier transform turns the backward shift into multiplication by `chi (-k)`. -/
