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

theorem pathF_eq_exp_mul_pathR (x : Fin (N + 1) → S) :
    P.pathF x = Real.exp (P.beta * (P.work x - P.deltaF)) * P.pathR (revPath x) := by
  have hZ0 : (0:ℝ) < P.Z 0 := P.Z_pos 0
  have hZN : (0:ℝ) < P.Z N := P.Z_pos N
  have hdF : Real.exp (P.beta * (P.work x - P.deltaF))
      = Real.exp (P.beta * P.work x) * (P.Z N / P.Z 0) := by
    rw [mul_sub, Real.exp_sub, P.exp_beta_deltaF]
    field_simp
  have hexp : Real.exp (-P.beta * P.E 0 (pt x 0))
        * Real.exp (P.beta * ∑ k ∈ range N,
            (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1))))
      = Real.exp (P.beta * P.work x) * Real.exp (-P.beta * P.E N (pt x N)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-P.beta) * P.work_telescope x
  rw [pathF, P.pathR_revPath x, gibbs, gibbs, P.prod_forward x, hdF]
  simp only [neg_mul] at hexp ⊢
  set A := ∏ k ∈ range N, P.K k (pt x (k + 1)) (pt x k) with hA
  set e := Real.exp (P.beta * ∑ k ∈ range N,
      (P.E (k + 1) (pt x k) - P.E (k + 1) (pt x (k + 1)))) with he
  field_simp
  linear_combination A * hexp

/-- Auxiliary: the reverse work distribution at `-w` is strictly positive as soon as some
trajectory realises the work value `w`. -/
