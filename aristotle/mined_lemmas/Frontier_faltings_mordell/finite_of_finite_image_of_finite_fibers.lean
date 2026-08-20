/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/

lemma finite_of_finite_image_of_finite_fibers {α β : Type*} {S : Set α} {f : α → β}
    (h : (f '' S).Finite) (hfib : ∀ b, {a | f a = b}.Finite) : S.Finite := by
  refine Set.Finite.subset (h.biUnion (fun b _ => hfib b)) ?_
  intro a ha
  exact Set.mem_biUnion (Set.mem_image_of_mem f ha) rfl

/-- Over `ℚ`, the `k`-th roots of a given number form a finite set (for `k > 0`). -/
