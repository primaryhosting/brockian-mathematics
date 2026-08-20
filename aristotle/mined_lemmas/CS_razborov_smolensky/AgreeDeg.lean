import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


def AgreeDeg (F : Type*) [Field F] {n : ℕ} (A : Finset (Fin n → Bool)) (d : ℕ) :
    Submodule F ((Fin n → Bool) → F) where
  carrier := {f | ∃ g ∈ Deg F n d, ∀ x ∈ A, g x = f x}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, fun x hx => by
      simp [Pi.add_apply, h₁ x hx, h₂ x hx]⟩
  zero_mem' := ⟨0, Submodule.zero_mem _, fun x _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨g, hg, h⟩
    exact ⟨c • g, Submodule.smul_mem _ _ hg, fun x hx => by
      simp [Pi.smul_apply, h x hx]⟩

