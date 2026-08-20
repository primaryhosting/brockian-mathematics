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

lemma le_configCount (q N : ℕ) (hq : 0 < q) :
    N * (N / q) ≤ configCount q N := by
  rw [configCount_eq_sum]
  calc N * (N / q) = ∑ _a ∈ Finset.range N, (N / q) := by simp
    _ ≤ ∑ a ∈ Finset.range N, ((Finset.range N).filter (fun b => b % q = a % q)).card :=
        Finset.sum_le_sum (fun a _ => le_card_residue q N (a % q) (Nat.mod_lt _ hq))

/-- The configuration count differs from the main term by at most `N`. -/
