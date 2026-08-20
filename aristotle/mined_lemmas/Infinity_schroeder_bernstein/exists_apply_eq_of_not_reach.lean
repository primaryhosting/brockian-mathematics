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

theorem exists_apply_eq_of_not_reach {x : X} (hx : ¬ Reach f g x) : ∃ y, g y = x :=
  Classical.byContradiction fun hc => hx (Reach.base x fun y hy => hc ⟨y, hy⟩)

/-- If `g y` is reachable, then `y` is in the image of `f` restricted to reachable points. -/
