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

theorem reach_of_apply_aux (hg : Function.Injective g) :
    ∀ {x : X}, Reach f g x → ∀ y : Y, x = g y → ∃ x', Reach f g x' ∧ f x' = y := by
  intro x hx
  induction hx with
  | base x hb => exact fun y hy => absurd hy.symm (hb y)
  | step x hx _ => exact fun y hy => ⟨x, hx, hg hy⟩

