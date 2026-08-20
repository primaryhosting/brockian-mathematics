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

theorem csbFun_injective (hf : Function.Injective f) :
    Function.Injective (csbFun f g) := by
  have key : ∀ x₁ x₂ : X, leftPart f g x₁ → ¬ leftPart f g x₂ →
      csbFun f g x₁ = csbFun f g x₂ → x₁ = x₂ := by
    intro x₁ x₂ h₁ h₂ heq
    have hx₂ : g (csbFun f g x₂) = x₂ := csbFun_of_not_leftPart f g h₂
    rw [csbFun_of_leftPart f g h₁] at heq
    rw [← heq] at hx₂
    exact absurd (hx₂ ▸ leftPart_step f g h₁) h₂
  intro x₁ x₂ heq
  by_cases h₁ : leftPart f g x₁ <;> by_cases h₂ : leftPart f g x₂
  · rw [csbFun_of_leftPart f g h₁, csbFun_of_leftPart f g h₂] at heq
    exact hf heq
  · exact key x₁ x₂ h₁ h₂ heq
  · exact (key x₂ x₁ h₂ h₁ heq.symm).symm
  · have e₁ := csbFun_of_not_leftPart f g h₁
    have e₂ := csbFun_of_not_leftPart f g h₂
    rw [heq] at e₁
    exact e₁.symm.trans e₂

