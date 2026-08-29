import Mathlib

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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem modProd_dvd_of_forall {q n X : ℕ} (hq : (n + 1).factorial ∣ q)
    (h : ∀ i ≤ n, modAt q i ∣ X) : modProd q n ∣ X := by
  have key : ∀ m : ℕ, m ≤ n + 1 → (∏ i ∈ Finset.range m, modAt q i) ∣ X := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        rw [Finset.prod_range_succ]
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (ih (by omega)) (h m (by omega))
        refine Nat.Coprime.prod_left (fun i hi => ?_)
        simp only [Finset.mem_range] at hi
        exact coprime_modAt hq (by omega) (by omega) (by omega)
  exact key (n+1) le_rfl

/-- Chinese remainder theorem for the moduli `modAt q i`, `i ≤ n`: any finite sequence of
residues is realised, by arbitrarily large numbers. -/
