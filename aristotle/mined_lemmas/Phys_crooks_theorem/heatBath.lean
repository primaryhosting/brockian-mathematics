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

noncomputable def heatBath (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ) :
    Setup S N where
  beta := beta
  beta_pos := hbeta
  E := E
  K := fun k _ y => Real.exp (-beta * E (k + 1) y) / ∑ s : S, Real.exp (-beta * E (k + 1) s)
  K_pos := fun k _ _ =>
    div_pos (Real.exp_pos _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty)
  detailed_balance := fun k x y => by ring

/-- The heat-bath kernels are genuine stochastic matrices. -/
