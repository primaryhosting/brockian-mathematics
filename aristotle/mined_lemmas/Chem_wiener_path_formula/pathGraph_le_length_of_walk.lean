/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
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

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

theorem pathGraph_le_length_of_walk {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    Nat.dist u.val v.val ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      have hb : Nat.dist a.val b.val = 1 := by
        rw [pathGraph_adj] at h
        rcases h with h | h <;> unfold Nat.dist <;> omega
      calc Nat.dist a.val c.val ≤ Nat.dist a.val b.val + Nat.dist b.val c.val :=
            Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + p.length := by rw [hb]; exact Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons h p).length := by simp [Nat.add_comm]

/-- The distance in the path graph is bounded above by the difference of indices. -/
