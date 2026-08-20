/-
# Fib Uniform Mod 5
Category: Cone Line
Target: Brockian.ConeLine.fib_uniform_mod5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- The list of the first twenty Fibonacci residues modulo `5`. -/
lemma fib_mod5_list :
    (List.range 20).map (fun k => Nat.fib k % 5)
      = [0, 1, 1, 2, 3, 0, 3, 3, 1, 4, 0, 4, 4, 3, 2, 0, 2, 2, 4, 1] := by
  decide

/-- The Pisano period seed: `fib 20 ≡ 0` and `fib 21 ≡ 1` modulo `5`. -/
theorem fib_pisano20_seed : Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1 := by
  constructor <;> decide

/-- Fibonacci is uniformly distributed modulo `5`: within one Pisano period
(20 terms) each residue class occurs exactly four times. -/
theorem fib_uniform_mod5 (r : Fin 5) :
    ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card = 4 := by
  have h : ((Finset.range 20).filter (fun k => Nat.fib k % 5 = r.val)).card
      = (List.range 20).countP (fun k => decide (Nat.fib k % 5 = r.val)) := by
    rw [List.countP_eq_length_filter]; rfl
  have hmap := List.countP_map (p := fun m => decide (m = r.val))
      (f := fun k => Nat.fib k % 5) (l := List.range 20)
  simp only [Function.comp_def] at hmap
  rw [h, ← hmap, fib_mod5_list]
  fin_cases r <;> rfl

end ConeLine
end Brockian

