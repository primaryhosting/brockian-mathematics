/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
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

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of "configurations" of size `N` at modulus `q`: ordered pairs `(a, b)` with
`a, b < N` and `a ≡ b [MOD q]`. -/

lemma le_card_residue (q N r : ℕ) (hr : r < q) :
    N / q ≤ ((Finset.range N).filter (fun b => b % q = r)).card := by
  classical
  have h : (Finset.range (N / q)).card
      ≤ ((Finset.range N).filter (fun b => b % q = r)).card := by
    apply Finset.card_le_card_of_injOn (fun k => q * k + r)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, by simp [Nat.mod_eq_of_lt hr]⟩
      have h1 : q * (k + 1) ≤ q * (N / q) := Nat.mul_le_mul_left q hk
      have h2 : q * (N / q) ≤ N := Nat.mul_div_le N q
      have h3 : q * k + q = q * (k + 1) := by ring
      omega
    · intro x _ y _ hxy
      have hxy' : q * x + r = q * y + r := hxy
      have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le r) hr
      have : q * x = q * y := by omega
      exact Nat.eq_of_mul_eq_mul_left hq this
  simpa using h

/-- Fiberwise decomposition of `configCount`. -/
