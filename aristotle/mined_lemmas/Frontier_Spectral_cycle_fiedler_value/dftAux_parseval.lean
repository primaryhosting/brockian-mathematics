/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as a plain block comment; its text is verbatim.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset Complex ZMod Matrix

/-! ## The Laplacian of the cycle graph -/

/-- The Laplacian matrix of the cycle graph `C n`, with vertex set `ZMod n`:
`2` on the diagonal, `-1` between neighbours `i` and `i ± 1`, `0` elsewhere. -/

lemma dftAux_parseval (x : ZMod n → ℂ) :
    ∑ k : ZMod n, ‖dftAux n x k‖ ^ 2 = n * ∑ j : ZMod n, ‖x j‖ ^ 2 := by
  have expand : ∀ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = ∑ j : ZMod n, ∑ l : ZMod n,
          (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l)) := by
    intro k
    rw [dftAux, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have hconj : (starRingEnd ℂ) ((stdAddChar (l * k) : ℂ) * x l)
        = (stdAddChar (-(l * k)) : ℂ) * (starRingEnd ℂ) (x l) := by
      rw [RingHom.map_mul, conj_stdAddChar]
    have hc : (stdAddChar (j * k) : ℂ) * stdAddChar (-(l * k)) = stdAddChar ((j - l) * k) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [hconj, ← hc]; ring
  have swap : ∑ k : ZMod n, ∑ j : ZMod n, ∑ l : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l))
      = ∑ j : ZMod n, ∑ l : ZMod n, ∑ k : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  have main : ∑ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = (n : ℂ) * ∑ j : ZMod n, x j * (starRingEnd ℂ) (x j) := by
    rw [Finset.sum_congr rfl (fun k _ => expand k), swap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have inner : ∀ l : ZMod n, ∑ k : ZMod n,
        (stdAddChar ((j - l) * k) : ℂ) * (x j * (starRingEnd ℂ) (x l))
        = (if l = j then (n : ℂ) else 0) * (x j * (starRingEnd ℂ) (x l)) := by
      intro l
      rw [← Finset.sum_mul, sum_stdAddChar]
      congr 1
      by_cases h : l = j
      · simp [h]
      · have hne : j - l ≠ 0 := fun hh => h (by linear_combination -hh)
        simp [h, hne]
    rw [Finset.sum_congr rfl (fun l _ => inner l)]
    simp
  have hL : ∑ k : ZMod n, dftAux n x k * (starRingEnd ℂ) (dftAux n x k)
      = ((∑ k : ZMod n, ‖dftAux n x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [Complex.mul_conj, Complex.sq_norm])
  have hR : ∑ j : ZMod n, x j * (starRingEnd ℂ) (x j)
      = ((∑ j : ZMod n, ‖x j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Complex.mul_conj, Complex.sq_norm])
  rw [hL, hR] at main
  exact_mod_cast main

