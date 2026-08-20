/-
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Finset Matrix SimpleGraph

namespace Frontier.Spectral

/-! ## The root of unity `ζ = exp (2 π i / n)` -/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma dft_inversion {n : ℕ} (hn : n ≠ 0) (y : Fin n → ℂ) (i : Fin n) :
    ∑ k : Fin n, dft n y ((k : ℕ) : ℤ) * zeta n ^ (((k : ℕ) : ℤ) * (i : ℕ)) = n * y i := by
  simp only [dft, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hiff : ∀ j : Fin n, ((n : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ↔ j = i := by
    intro j
    constructor
    · intro hdvd
      have h1 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (n : ℤ) := by
        have := i.isLt; have := j.isLt
        rw [abs_lt]; constructor <;> omega
      have h2 := Int.eq_zero_of_abs_lt_dvd hdvd h1
      exact Fin.ext (by omega)
    · rintro rfl; simp
  have step : ∀ j : Fin n, ∑ k : Fin n,
      y j * zeta n ^ (-(((k : ℕ) : ℤ) * (j : ℕ))) * zeta n ^ (((k : ℕ) : ℤ) * (i : ℕ))
      = y j * (if j = i then (n : ℂ) else 0) := by
    intro j
    rw [← if_congr (hiff j) rfl rfl, ← zeta_char_sum hn (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← zpow_add₀ (zeta_ne_zero n)]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun j _ => step j]
  simp [Finset.sum_ite_eq', mul_comm]

