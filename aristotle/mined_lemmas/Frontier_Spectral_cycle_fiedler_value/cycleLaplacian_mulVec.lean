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

lemma cycleLaplacian_mulVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : ZMod n → ℝ) (i : ZMod n) :
    (cycleLaplacian n *ᵥ x) i = 2 * x i - x (i + 1) - x (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h2 : (2 : ZMod n) ≠ 0 := two_ne_zero_zmod hn
  have hne1 : i + 1 ≠ i := by intro h; apply h1; linear_combination h
  have hne2 : i - 1 ≠ i := by intro h; apply h1; linear_combination -h
  have hne3 : i + 1 ≠ i - 1 := by intro h; apply h2; linear_combination h
  have key : ∀ j : ZMod n, cycleLaplacian n i j * x j =
      (if j = i then 2 * x j else 0) + (if j = i + 1 then -x j else 0)
        + (if j = i - 1 then -x j else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp [cycleLaplacian, Ne.symm hne1, Ne.symm hne2]
    · by_cases hj2 : j = i + 1
      · subst hj2
        simp [cycleLaplacian, hji, hne3, h1]
      · by_cases hj3 : j = i - 1
        · subst hj3
          have e1 : i = i - 1 + 1 := by ring
          simp [cycleLaplacian, hji, hj2, ← e1, Ne.symm hne2]
        · have c1 : i ≠ j := fun h => hji h.symm
          have c2 : ¬ (i = j + 1) := by
            intro h; exact hj3 (by rw [h]; ring)
          simp [cycleLaplacian, c1, c2, hji, hj2, hj3]
  rw [Matrix.mulVec]
  simp only [dotProduct, key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp
  ring

