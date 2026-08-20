/-!
# Schroeder Bernstein
Category: Frontier — Set Theory
Target: Infinity.schroeder_bernstein
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

universe u v

variable {X : Type u} {Y : Type v}

/-- `Reach f g` is the smallest predicate on `X` containing every element outside the
range of `g` and closed under `x ↦ g (f x)`.  It is the classical "back-and-forth"
set used in the proof of the Cantor–Schröder–Bernstein theorem. -/
inductive Reach (f : X → Y) (g : Y → X) : X → Prop
  | base (x : X) (h : ∀ y, g y ≠ x) : Reach f g x
  | step (x : X) (h : Reach f g x) : Reach f g (g (f x))

variable {f : X → Y} {g : Y → X}

/-- Every element not in `Reach f g` lies in the range of `g`. -/

theorem sbMap_surjective (hg : Function.Injective g) :
    Function.Surjective (sbMap f g) := by
  intro y
  by_cases h : Reach f g (g y)
  · obtain ⟨x, hx, hfx⟩ := reach_of_apply hg h
    exact ⟨x, by rw [sbMap_of_reach hx, hfx]⟩
  · refine ⟨g y, ?_⟩
    exact hg (sbMap_of_not_reach h)

/-- **Cantor–Schröder–Bernstein**: if there is an injection `f : X → Y` and an injection
`g : Y → X`, then there is a bijection between `X` and `Y`. -/
