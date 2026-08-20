/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma cycle20_adj_iff (j m : Fin 20) :
    (SimpleGraph.cycleGraph 20).Adj j m ↔ (m = j - 1 ∨ m = j + 1) := by
  have h : (SimpleGraph.cycleGraph 20).Adj j m ↔ (j - m = 1 ∨ m - j = 1) :=
    SimpleGraph.cycleGraph_adj (n := 18)
  rw [h]
  constructor
  · rintro (h1 | h1)
    · left; rw [← h1]; abel
    · right; rw [← h1]; abel
  · rintro (h1 | h1) <;> subst h1
    · left; abel
    · right; abel

