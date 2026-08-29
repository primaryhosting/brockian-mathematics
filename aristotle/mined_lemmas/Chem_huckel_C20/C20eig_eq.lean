/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₂₀`, indexed by `Fin 20`
(whose addition is addition modulo `20`). -/

lemma C20eig_eq (k : Fin 20) : C20eig k = zeta20 ^ k.val + zeta20 ^ (19 * k.val) := by
  have hx : zeta20 ^ k.val = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta20, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [C20eig, zeta20_pow_inv, hx, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos]
  ring_nf

