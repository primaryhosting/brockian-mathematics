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

lemma PR_pos (w : ℝ) (h : ∃ x : Fin (N + 1) → S, P.work x = w) : 0 < P.PR (-w) := by
  obtain ⟨x, hx⟩ := h
  refine Finset.sum_pos (fun y _ => P.pathR_pos y) ⟨revPath x, ?_⟩
  simp [Finset.mem_filter, P.workRev_revPath x, hx]

omit [Nonempty S] in
/-- Reindexing the forward trajectories with work `w` by time reversal. -/
