import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid. -/

theorem charPoly_eq_zero_of_isLoop (M : Matroid α) (E : Finset α) (e : α) (heE : e ∈ E)
    (he : M.IsLoop e) : charPoly M E = 0 := by
  classical
  have hins : ∀ S : Set α, M.eRk (insert e S) = M.eRk S := fun S => by
    rw [← M.eRk_insert_closure_eq e S, Set.insert_eq_self.2 (he.mem_closure S), M.eRk_closure_eq]
  have hE : E = insert e (E.erase e) := (Finset.insert_erase heE).symm
  rw [charPoly, show E.powerset = (insert e (E.erase e)).powerset from by rw [← hE],
    Finset.sum_powerset_insert (Finset.notMem_erase e E), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  have het : e ∉ t := fun h => (Finset.notMem_erase e E) (Finset.mem_powerset.mp ht h)
  have hcard : (insert e t).card = t.card + 1 := Finset.card_insert_of_notMem het
  have hrank : natRank M ((insert e t : Finset α) : Set α) = natRank M (t : Set α) := by
    rw [natRank, natRank, Finset.coe_insert, hins]
  rw [hcard, hrank, pow_succ]
  ring

/-- A matroid with a loop also satisfies the log-concavity conclusion (its characteristic
polynomial is identically zero). -/
