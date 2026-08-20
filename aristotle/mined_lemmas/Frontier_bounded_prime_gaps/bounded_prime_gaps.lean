import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
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

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/

theorem bounded_prime_gaps :
    BoundedPrimeGaps ↔ Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, iSup_lt_top_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    rw [iInf_ge_le_coe_iff]
    obtain ⟨n, hn, hle⟩ := (infinite_setOf_iff _).mp hB N
    exact ⟨n, hn, by exact_mod_cast hle⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, (infinite_setOf_iff _).mpr fun N => ?_⟩
    obtain ⟨n, hn, hle⟩ := (iInf_ge_le_coe_iff _ N B).mp (hB N)
    exact ⟨n, hn, by exact_mod_cast hle⟩

/-! ### Unconditional facts about prime gaps -/

/-- Prime gaps are positive: `p_{n+1} > p_n`. -/
