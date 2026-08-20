import Mathlib

/-!
# Construction of an Aronszajn tree

We build the classical (special) Aronszajn tree: nodes at level `α < ω₁` are strictly
increasing bounded functions `α → ℚ`, constructed by transfinite recursion so that each
level is countable and every node can be extended to any higher level while keeping a
prescribed rational bound.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node is (the total extension by `0` of) a function from a countable ordinal to `ℚ`. -/
abbrev Nd : Type 1 := Ordinal.{0} → ℚ

/-- `SBd f α q` says the values of `f` below `α` are bounded by some rational `< q`. -/

theorem succ_ext {δ : Ordinal.{0}} (f₁ : Nd) (hf₁ : f₁ ∈ L δ) (Q : ℚ) (hQ : SBd f₁ δ Q) :
    ∃ g ∈ L (δ + 1), (∀ γ < δ, g γ = f₁ γ) ∧ SBd g (δ + 1) Q := by
  obtain ⟨r, hrQ, hr⟩ := hQ
  refine ⟨snoc δ f₁ ((r + Q) / 2), ?_, ?_, ?_⟩
  · rw [L_succ]
    exact ⟨f₁, hf₁, (r + Q) / 2, fun γ hγ => lt_of_le_of_lt (hr γ hγ) (by linarith), rfl⟩
  · intro γ hγ
    exact snoc_of_lt hγ
  · refine ⟨(r + Q) / 2, by linarith, ?_⟩
    intro γ hγ
    rcases lt_or_eq_of_le (lt_succ_iff'.mp hγ) with h | rfl
    · rw [snoc_of_lt h]; linarith [hr γ h]
    · rw [snoc_self]

