import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma eval_exactlyOne (m : ℕ) (f : Fin m → Circuit ι) (v : ι → Bool) :
    (exactlyOne m f).eval v = true ↔ ∃! a, (f a).eval v = true := by
  rw [exactlyOne, eval, Bool.and_eq_true, eval_atLeastOne, eval_atMostOne]
  constructor
  · rintro ⟨⟨a, ha⟩, h2⟩
    exact ⟨a, ha, fun b hb => h2 b a hb ha⟩
  · rintro ⟨a, ha, h2⟩
    exact ⟨⟨a, ha⟩, fun b c hb hc => by rw [h2 b hb, h2 c hc]⟩

