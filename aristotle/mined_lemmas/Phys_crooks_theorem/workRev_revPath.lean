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

lemma workRev_revPath (x : Fin (N + 1) → S) : P.workRev (revPath x) = -P.work x := by
  rw [workRev, work, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_range_reflect (fun j => -(P.E (j + 1) (pt x j) - P.E j (pt x j))) N]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := Finset.mem_range.mp hk
  have h1 : pt (revPath x) (k + 1) = pt x (N - (k + 1)) := pt_revPath x (by omega)
  have h2 : N - 1 - k + 1 = N - k := by omega
  have h3 : N - 1 - k = N - (k + 1) := by omega
  rw [h1, h2, h3]
  ring

omit [Nonempty S] in
