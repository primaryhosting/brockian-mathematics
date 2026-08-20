/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

section CSB

variable {X : Type u} {Y : Type v}

/-- `iterateFun F n x` is the `n`-fold application of `F` to `x`. -/

theorem schroeder_bernstein_inverse {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (h : X → Y) (k : Y → X), (∀ x, k (h x) = x) ∧ (∀ y, h (k y) = y) := by
  obtain ⟨h, hinj, hsurj⟩ := schroeder_bernstein hf hg
  refine ⟨h, fun y => Classical.choose (hsurj y), fun x => ?_, fun y => ?_⟩
  · exact hinj (Classical.choose_spec (hsurj (h x)))
  · exact Classical.choose_spec (hsurj y)

end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder Bernstein — Mathlib cross-check

The main statement `Infinity.schroeder_bernstein` is proved from first principles (see
`RequestProject/SchroederBernstein.lean`, whose required header comment prevents any `import`).
Here we record the corresponding `Equiv`-valued statement, and check it against Mathlib's own
`Function.Embedding.antisymm`.
-/

namespace Infinity

/-- Cantor-Schröder-Bernstein, packaged as an equivalence, derived from
`Infinity.schroeder_bernstein`. -/
