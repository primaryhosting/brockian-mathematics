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

lemma heatBath_stochastic (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ)
    (k : ℕ) (x : S) : ∑ y : S, (heatBath N beta hbeta E).K k x y = 1 := by
  have hZ : (0:ℝ) < ∑ s : S, Real.exp (-beta * E (k + 1) s) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty
  simp only [heatBath, ← Finset.sum_div]
  exact div_self (ne_of_gt hZ)

end Examples

/-- **Crooks fluctuation theorem**: for every work value `w` that is realised by some
trajectory, the ratio of the forward work distribution at `w` and the reverse work distribution
at `-w` equals `e^{β(W-ΔF)}`. -/
