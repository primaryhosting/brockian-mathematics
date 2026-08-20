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

lemma card_residue_le (q N r : ℕ) :
    ((Finset.range N).filter (fun b => b % q = r)).card ≤ N / q + 1 := by
  classical
  have h : ((Finset.range N).filter (fun b => b % q = r)).card
      ≤ (Finset.range (N / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun b => b / q)
    · intro b hb
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hb.1.le)
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      have hxy' : x / q = y / q := hxy
      have hx' : q * (x / q) + x % q = x := Nat.div_add_mod x q
      have hy' : q * (y / q) + y % q = y := Nat.div_add_mod y q
      calc x = q * (x / q) + x % q := hx'.symm
        _ = q * (y / q) + y % q := by rw [hxy', hx.2, hy.2]
        _ = y := hy'
  simpa using h

/-- In `[0, N)` there are at least `N / q` integers in a fixed residue class mod `q`. -/
