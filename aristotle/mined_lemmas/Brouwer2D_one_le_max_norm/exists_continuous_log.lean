/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

theorem exists_continuous_log (g : C(ℂ, ℂ)) (hg : ∀ z, g z ≠ 0) :
    ∃ G : C(ℂ, ℂ), ∀ z, Complex.exp (G z) = g z := by
  obtain ⟨G, ⟨-, hG⟩, -⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g
      (a₀ := (0 : ℂ)) (e₀ := Complex.log (g 0)) (Complex.exp_log (hg 0))
      (fun a => by simpa using hg a)
  exact ⟨G, fun z => congrFun hG z⟩

/-! ### The key positivity estimate on the boundary circle -/

/-- If `z` lies on the unit circle and `w` lies in the closed unit disk with `w ≠ z`, then
`z - w` points strictly into the half plane determined by `z`. -/
