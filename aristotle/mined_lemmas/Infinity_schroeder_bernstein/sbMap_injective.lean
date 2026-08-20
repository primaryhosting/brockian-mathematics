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

theorem sbMap_injective (hf : Function.Injective f) :
    Function.Injective (sbMap f g) := by
  intro x₁ x₂ hx
  by_cases h₁ : Reach f g x₁ <;> by_cases h₂ : Reach f g x₂
  · rw [sbMap_of_reach h₁, sbMap_of_reach h₂] at hx
    exact hf hx
  · exfalso
    have h : g (sbMap f g x₂) = x₂ := sbMap_of_not_reach h₂
    rw [← hx, sbMap_of_reach h₁] at h
    exact h₂ (h ▸ Reach.step x₁ h₁)
  · exfalso
    have h : g (sbMap f g x₁) = x₁ := sbMap_of_not_reach h₁
    rw [hx, sbMap_of_reach h₂] at h
    exact h₁ (h ▸ Reach.step x₂ h₂)
  · have e₁ : g (sbMap f g x₁) = x₁ := sbMap_of_not_reach h₁
    have e₂ : g (sbMap f g x₂) = x₂ := sbMap_of_not_reach h₂
    rw [← e₁, ← e₂, hx]

