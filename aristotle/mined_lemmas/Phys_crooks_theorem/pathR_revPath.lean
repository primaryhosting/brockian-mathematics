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

lemma pathR_revPath (x : Fin (N + 1) → S) :
    P.pathR (revPath x)
      = P.gibbs N (pt x N) * ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) := by
  rw [pathR]
  congr 1
  · rw [pt_revPath x (Nat.zero_le N), Nat.sub_zero]
  · rw [← Finset.prod_range_reflect (fun j => P.K j (pt x (j + 1)) (pt x j)) N]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < N := Finset.mem_range.mp hk
    have h1 : pt (revPath x) k = pt x (N - k) := pt_revPath x (by omega)
    have h2 : pt (revPath x) (k + 1) = pt x (N - (k + 1)) := pt_revPath x (by omega)
    have h3 : N - 1 - k + 1 = N - k := by omega
    have h4 : N - 1 - k = N - (k + 1) := by omega
    rw [h1, h2, h3, h4]

omit [Nonempty S] in
