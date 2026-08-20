import Mathlib

/-!
# Five Color Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.five_color_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

variable {V : Type*} [DecidableEq V]

/-- The neighbours of `v` inside the vertex set `s`. -/

lemma Reduces.subset {s : Finset V} {G : SimpleGraph V} {t : Finset V} {H : SimpleGraph V}
    (h : Reduces s G t H) : t ⊆ s := by
  induction h with
  | refl s G => exact Finset.Subset.refl s
  | del v _ ih => exact ih.trans (Finset.erase_subset _ _)
  | con v u w hu hw huw hnadj _ ih =>
      exact ih.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))

/-- The base case of the five colour theorem: a graph on at most five vertices satisfies the
reduction hypothesis (all degrees stay at most `4`). -/
