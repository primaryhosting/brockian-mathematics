import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

set_option grind.warning false

namespace Frontier

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

theorem trace_pow_eq_sum_cycles {S : Type} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℝ) (m : ℕ) :
    Matrix.trace (T ^ (m + 1)) =
      ∑ h : Fin (m + 1) → S, ∏ i : Fin (m + 1), T (h i) (h (i + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => S)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_apply_eq_sum_paths T m x x]
  refine Finset.sum_congr rfl fun f _ => ?_
  show _ = ∏ i : Fin (m + 1), _
  rw [Fin.prod_univ_castSucc]
  simp [Fin.coeSucc_eq_succ, Fin.last_add_one, Fin.consEquiv]

/-- The bond sum of a configuration, organised row by row. -/
