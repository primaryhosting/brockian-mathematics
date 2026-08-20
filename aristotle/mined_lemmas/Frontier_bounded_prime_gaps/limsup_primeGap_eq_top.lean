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

theorem limsup_primeGap_eq_top :
    Filter.limsup (fun n => (primeGap n : ℕ∞)) atTop = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine eq_top_iff.mpr (le_iInf fun N => ?_)
  by_contra hcon
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp (fun h => hcon (h ▸ le_rfl))
  obtain ⟨n, hn, hgt⟩ := exists_ge_primeGap_gt B N
  have hle : ((primeGap n : ℕ) : ℕ∞) ≤ (B : ℕ∞) := by
    refine le_trans (le_trans (le_iSup (f := fun _ : n ≥ N => ((primeGap n : ℕ) : ℕ∞)) hn)
      (le_iSup (fun i => ⨆ _ : i ≥ N, ((primeGap i : ℕ) : ℕ∞)) n)) ?_
    exact le_of_eq hB.symm
  have := Nat.cast_le.mp hle
  omega

end Frontier

