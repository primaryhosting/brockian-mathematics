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

lemma exp_beta_deltaF : Real.exp (P.beta * P.deltaF) = P.Z 0 / P.Z N := by
  have hb : P.beta ≠ 0 := ne_of_gt P.beta_pos
  have h1 : P.beta * P.deltaF = -Real.log (P.Z N / P.Z 0) := by
    rw [deltaF]; field_simp
  rw [h1, Real.exp_neg, Real.exp_log (div_pos (P.Z_pos N) (P.Z_pos 0)), inv_div]

/-- **Microscopic reversibility**: the ratio of the probability of a forward trajectory to that of
its time reverse under the reverse protocol is `exp (β (W - ΔF))`. -/
