/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

lemma eigenvalue_eq (k : ℕ) :
    ee (k : ZMod 17) + ee (-(k : ZMod 17))
      = ((2 * Real.cos (2 * Real.pi * k / 17) : ℝ) : ℂ) := by
  have hom : om ^ k = Complex.exp ((2 * Real.pi * k / 17 : ℝ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 : ee ((k : ℕ) : ZMod 17) = Complex.exp ((2 * Real.pi * k / 17 : ℝ) * Complex.I) := by
    rw [ee_natCast, hom]
  have h2 : ee (-((k : ℕ) : ZMod 17))
      = Complex.exp (-((2 * Real.pi * k / 17 : ℝ) * Complex.I)) := by
    rw [ee_neg, h1, ← Complex.exp_neg]
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat, Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₇`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 17 vertices if and only if it is of the form
`2 cos (2πk/17)` for some `k ∈ {0, …, 16}`. -/
