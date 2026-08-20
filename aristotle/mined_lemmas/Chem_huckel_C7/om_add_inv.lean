/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Hückel theory for the cycle `C₇`

In Hückel molecular orbital theory the (reduced) Hamiltonian of a conjugated
cyclic polyene `Cₙ` is the adjacency matrix of the cycle graph `Cₙ`, and the
orbital energies are `α + β λ` where `λ` runs over the adjacency eigenvalues.
For `n = 7` (the cycloheptatrienyl system) the eigenvalues are
`2 cos (2πk/7)`, `k = 0, …, 6`.

The proof diagonalises the adjacency matrix by the discrete Fourier
(Vandermonde) matrix built from `ω = exp (2πi/7)`.
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The primitive 7-th root of unity `ω = exp (2πi/7)`. -/

theorem om_add_inv (k : Fin 7) :
    om ^ (k : ℕ) + (om ^ (k : ℕ)) ^ 6 = huckelVal k := by
  set t : ℝ := 2 * Real.pi * k / 7 with ht
  rw [om_pow_eq_exp k, ← Complex.exp_nat_mul]
  have h7 : Complex.exp ((7 : ℕ) * ((t : ℂ) * Complex.I)) = 1 := by
    have h : ((7 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = ((k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [ht]; push_cast; ring
    rw [h]
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℕ)
  have h6 : Complex.exp ((6 : ℕ) * ((t : ℂ) * Complex.I))
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h : ((6 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = ((7 : ℕ) * ((t : ℂ) * Complex.I)) + (-((t : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [h, Complex.exp_add, h7, one_mul]
  rw [h6, huckelVal, ht]
  push_cast
  rw [Complex.cos]
  ring_nf

