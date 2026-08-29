import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
-- `open scoped Classical` is omitted here: it overrides the graph's own `DecidableRel`
-- instances and makes `if`-congruence rewriting fail below.
-- open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open SimpleGraph Matrix Finset

section Combinatorics

variable {m : ℕ}

/-- Adjacency in the cycle graph on `Fin (m+1)` (with `m ≥ 2`) in additive form. -/

lemma cycleGraph_adj_iff (hm : 2 ≤ m) (u v : Fin (m + 1)) :
    (cycleGraph (m + 1)).Adj u v ↔ (v = u + 1 ∨ u = v + 1) := by
  have h1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ a b : Fin (m + 1), (a - b).val = 1 ↔ a = b + 1 := by
    intro a b
    have e : ((a - b).val = ((1 : Fin (m + 1)).val)) ↔ (a - b = 1) := Fin.val_inj
    rw [h1] at e
    rw [e, sub_eq_iff_eq_add, add_comm (1 : Fin (m + 1)) b]
  rw [SimpleGraph.cycleGraph_adj', key, key]
  tauto

/-- In `Fin (m+1)` with `m ≥ 2`, the two cyclic neighbours of a vertex are distinct. -/
