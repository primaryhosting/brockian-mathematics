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

lemma sum_pathR_revPath (w : ℝ) :
    ∑ x ∈ univ.filter (fun x : Fin (N + 1) → S => P.work x = w), P.pathR (revPath x)
      = ∑ y ∈ univ.filter (fun y : Fin (N + 1) → S => P.workRev y = -w), P.pathR y := by
  refine Finset.sum_nbij' (i := revPath) (j := revPath) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hw : P.work x = w := by simpa using (Finset.mem_filter.mp hx).2
    simp [Finset.mem_filter, P.workRev_revPath x, hw]
  · intro y hy
    have hw : P.workRev y = -w := by simpa using (Finset.mem_filter.mp hy).2
    have hrr := P.workRev_revPath (revPath y)
    rw [revPath_revPath] at hrr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  · intro x _; simp
  · intro y _; simp
  · intro x _; rfl

/-- Crooks fluctuation theorem, product form: `P_F(W) = e^{β(W-ΔF)} P_R(-W)`. -/
