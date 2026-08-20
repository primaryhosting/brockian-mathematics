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

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all
unordered pairs of distinct vertices (represented as ordered pairs `u < v`). -/

lemma pathGraph_le_walk_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rcases abs_cases (((a : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (((b : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      omega

