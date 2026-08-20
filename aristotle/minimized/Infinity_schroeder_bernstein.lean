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

theorem reach_of_apply_aux (hg : Function.Injective g) :
    ∀ {x : X}, Reach f g x → ∀ y : Y, x = g y → ∃ x', Reach f g x' ∧ f x' = y := by
  intro x hx
  induction hx with
  | base x hb => exact fun y hy => absurd hy.symm (hb y)
  | step x hx _ => exact fun y hy => ⟨x, hx, hg hy⟩

theorem reach_of_apply (hg : Function.Injective g) {y : Y} (h : Reach f g (g y)) :
    ∃ x, Reach f g x ∧ f x = y :=
  reach_of_apply_aux hg h y rfl

open Classical in
/-- The bijection produced by the Cantor–Schröder–Bernstein construction:
use `f` on the reachable part of `X`, and the inverse of `g` elsewhere. -/

noncomputable def sbMap (f : X → Y) (g : Y → X) (x : X) : Y :=
  if hx : Reach f g x then f x else Classical.choose (exists_apply_eq_of_not_reach hx)

theorem sbMap_of_reach {x : X} (hx : Reach f g x) : sbMap f g x = f x := by
  simp [sbMap, hx]

theorem sbMap_of_not_reach {x : X} (hx : ¬ Reach f g x) :
    g (sbMap f g x) = x := by
  have h : sbMap f g x = Classical.choose (exists_apply_eq_of_not_reach hx) := by
    simp [sbMap, hx]
  rw [h]
  exact Classical.choose_spec (exists_apply_eq_of_not_reach hx)

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

theorem schroeder_bernstein {X : Type u} {Y : Type v} {f : X → Y} {g : Y → X}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ h : X → Y, Function.Injective h ∧ Function.Surjective h :=
  ⟨sbMap f g, sbMap_injective hf, sbMap_surjective hg⟩

end Infinity

import Mathlib
import RequestProject.SchroederBernstein

/-!
# Schroeder–Bernstein, Mathlib form

A restatement of `Infinity.schroeder_bernstein` in terms of Mathlib's `Equiv`,
obtained from `Function.Embedding.antisymm` (which is built on
`Function.Embedding.schroeder_bernstein`).
-/

namespace Infinity

/-- **Cantor–Schröder–Bernstein**, Mathlib form: injections both ways give an equivalence. -/
