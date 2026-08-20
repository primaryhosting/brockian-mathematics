import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem map (φ : G →* H) (hφ : ∀ (g : G) (x : X), φ g • x = g • x) (hP : Paradoxical G A) :
    Paradoxical H A := by
  obtain ⟨A₁, A₂, hunion, hd, h₁, h₂⟩ := hP
  exact ⟨A₁, A₂, hunion, hd, h₁.map φ hφ, h₂.map φ hφ⟩

end Paradoxical

/-- Absorbing a "small" set `D` into `A` using an element `g` whose iterates move `D` to
disjoint copies of itself inside `A`. -/
