/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma mu_eq (k : Fin 8) : mu k = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 8) := by
  have hz : zeta ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz7 : zeta ^ (7 * (k : ℕ))
      = Complex.exp (-((2 * Real.pi * (k : ℕ) / 8 : ℝ) * Complex.I)) := by
    have hmul : zeta ^ (7 * (k : ℕ)) * zeta ^ (k : ℕ) = 1 := by
      rw [← pow_add, show 7 * (k : ℕ) + (k : ℕ) = (k : ℕ) * 8 from by ring,
        zeta_pow_mul_eight]
    rw [Complex.exp_neg, ← hz]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [mu, hz, hz7, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- **Hückel theory for cyclooctatetraene / the cycle graph `C₈`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₈`
if and only if `μ = 2 cos (2πk/8)` for some `k ∈ {0, …, 7}`. -/
