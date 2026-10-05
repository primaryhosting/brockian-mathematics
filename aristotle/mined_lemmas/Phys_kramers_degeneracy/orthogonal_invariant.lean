/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space `V`: an antiunitary
(antilinear, inner-product-conjugating) involution-up-to-sign with `Θ ∘ Θ = -1`,
which is the situation of a half-integer-spin system. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  /-- Additivity. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Antilinearity. -/
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- Antiunitarity: `⟪Θ x, Θ y⟫ = conj ⟪x, y⟫ = ⟪y, x⟫`. -/
  inner_map' : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- Half-integer spin: `Θ² = -1`. -/
  sq_eq_neg' : ∀ x, toFun (toFun x) = -x

namespace TimeReversal

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

variable (Θ : TimeReversal V)


lemma orthogonal_invariant {U : Submodule ℂ V} (hU : ∀ x ∈ U, Θ x ∈ U) :
    ∀ x ∈ Uᗮ, Θ x ∈ Uᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  have h1 : ⟪Θ (Θ u), Θ x⟫_ℂ = ⟪x, Θ u⟫_ℂ := Θ.inner_map _ _
  rw [Θ.sq_eq_neg, inner_neg_left] at h1
  have h2 : ⟪Θ u, x⟫_ℂ = 0 := hx _ (hU u hu)
  have h3 : ⟪x, Θ u⟫_ℂ = 0 := by
    rw [← inner_conj_symm, h2]
    simp
  rw [h3] at h1
  linear_combination (norm := ring_nf) -h1

/-- **Even degeneracy.** In a finite-dimensional space, every `Θ`-invariant subspace has
even dimension, when `Θ² = -1`.  This is the strong form of Kramers' theorem, proved by
strong induction on the dimension: one splits off the two-dimensional `Θ`-invariant plane
spanned by `ψ` and `Θ ψ`. -/
