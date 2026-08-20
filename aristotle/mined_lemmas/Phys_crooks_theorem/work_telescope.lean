import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Statement: Crooks fluctuation theorem: P_F(W)/P_R(−W) = e^{β(W−ΔF)}.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Real
open scoped Classical

namespace Phys

variable {S : Type*} [Fintype S] [Nonempty S] {N : ℕ}

/-- `pt x k` is the state of the trajectory `x` (of length `N + 1`) at time `k`. -/

lemma work_telescope (x : Fin (N + 1) → S) :
    P.work x - ∑ k ∈ range N, (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))
      = P.E N (pt x N) - P.E 0 (pt x 0) := by
  rw [work, ← Finset.sum_sub_distrib]
  have h : ∀ k ∈ range N,
      (P.E (k + 1) (pt x k) - P.E k (pt x k))
        - (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))
      = (fun j => P.E j (pt x j)) (k + 1) - (fun j => P.E j (pt x j)) k := by
    intro k _; ring
  rw [Finset.sum_congr rfl h]
  exact Finset.sum_range_sub (fun j => P.E j (pt x j)) N

