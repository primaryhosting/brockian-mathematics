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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem cyclic_sum_prod_eq_trace {S : Type} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℝ) (j : ℕ) :
    ∑ r : Fin (j + 1) → S, ∏ i : Fin (j + 1), T (r i) (r (i + 1))
      = Matrix.trace (T ^ (j + 1)) := by
  have hsplit : ∀ r : Fin (j + 1) → S, (∏ i : Fin (j + 1), T (r i) (r (i + 1)))
      = T (r (Fin.last j)) (r 0) * ∏ i : Fin j, T (r i.castSucc) (r i.succ) := by
    intro r
    rw [Fin.prod_univ_castSucc, Fin.last_add_one, mul_comm]
    exact congrArg _ (Finset.prod_congr rfl (fun i _ => by rw [Fin.coeSucc_eq_succ]))
  simp_rw [hsplit]
  rw [sum_path_prod_eq_trace T T j, ← pow_succ']

/-- The partition function is the sum, over all sequences of row states, of the products of
transfer-matrix entries along the (cyclically closed) sequence. -/
