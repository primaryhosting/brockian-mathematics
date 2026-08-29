import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file contains auxiliary material used in the construction of an Aronszajn tree:
basic facts about countable ordinals, a dependent-choice helper, and the key
"extension" lemma for almost-disjoint modifications of injections into `ℕ`.
-/

namespace Aronszajn

open Set Cardinal Ordinal
open scoped Ordinal

/-! ### Countability of initial segments -/

/-- An initial segment of the ordinals is countable iff it lies below `ω₁`. -/

theorem exists_extend {α β : Ordinal.{0}} (hαβ : α ≤ β) (fβ g : Ordinal.{0} → ℕ) {R : Set ℕ}
    (hR : R.Finite) (hinj : Set.InjOn fβ (Set.Iio β)) (hcoinf : CoInf β fβ)
    (hg : Set.InjOn g (Set.Iio α)) (hdiff : (diffSet α g fβ).Finite)
    (hgR : ∀ γ < α, g γ ∉ R) :
    ∃ h : Ordinal.{0} → ℕ, (∀ γ < α, h γ = g γ) ∧ Set.InjOn h (Set.Iio β) ∧
      (diffSet β h fβ).Finite ∧ (∀ γ < β, h γ ∉ R) := by
  classical
  set D : Set Ordinal.{0} := diffSet α g fβ with hD
  -- the finite set of "bad values"
  set B : Set ℕ := g '' D ∪ R with hB
  have hBfin : B.Finite := (hdiff.image g).union hR
  -- the finite set of points of `[α, β)` that need repairing
  set E : Set Ordinal.{0} := {δ | δ < β ∧ α ≤ δ ∧ fβ δ ∈ B} with hE
  have hEfin : E.Finite := by
    apply Set.Finite.of_finite_image (f := fβ)
    · exact hBfin.subset (by rintro n ⟨δ, hδ, rfl⟩; exact hδ.2.2)
    · exact hinj.mono (fun δ hδ => hδ.1)
  -- the infinite set of "fresh values"
  set S : Set ℕ := (fβ '' Set.Iio β ∪ g '' Set.Iio α ∪ R)ᶜ with hS
  have hgsub : g '' Set.Iio α ⊆ fβ '' Set.Iio β ∪ g '' D := by
    intro n hn
    rcases image_subset_of_diffSet α fβ g hn with h | h
    · exact Or.inl (Set.image_mono (Set.Iio_subset_Iio hαβ) h)
    · refine Or.inr ?_
      rw [hD, diffSet_comm]
      exact h
  have hSinf : S.Infinite := by
    have h1 : ((fβ '' Set.Iio β)ᶜ \ (g '' D ∪ R)) ⊆ S := by
      intro n hn
      rw [hS]
      intro hmem
      rcases hmem with hmem | hmem
      · rcases hmem with hmem | hmem
        · exact hn.1 hmem
        · rcases hgsub hmem with h | h
          · exact hn.1 h
          · exact hn.2 (Or.inl h)
      · exact hn.2 (Or.inr hmem)
    exact (hcoinf.diff ((hdiff.image g).union hR)).mono h1
  have hSnot : ∀ n ∈ S, n ∉ fβ '' Set.Iio β ∧ n ∉ g '' Set.Iio α ∧ n ∉ R := by
    intro n hn
    rw [hS, Set.mem_compl_iff] at hn
    exact ⟨fun h => hn (Or.inl (Or.inl h)), fun h => hn (Or.inl (Or.inr h)),
      fun h => hn (Or.inr h)⟩
  obtain ⟨r, hrinj, hrS⟩ := exists_injOn_into_infinite hEfin hSinf
  set h : Ordinal.{0} → ℕ := fun γ => if γ < α then g γ else if γ ∈ E then r γ else fβ γ with hdef
  have hlow : ∀ γ < α, h γ = g γ := by intro γ hγ; simp [hdef, hγ]
  have hmid : ∀ γ ∈ E, ¬ γ < α → h γ = r γ := by
    intro γ hγ hγα; simp [hdef, hγ, hγα]
  have hhigh : ∀ γ, ¬ γ < α → γ ∉ E → h γ = fβ γ := by
    intro γ hγα hγ; simp [hdef, hγ, hγα]
  have hnotB : ∀ γ, γ < β → ¬ γ < α → γ ∉ E → fβ γ ∉ B := by
    intro γ hγβ hγα hγE hmem
    exact hγE ⟨hγβ, not_lt.1 hγα, hmem⟩
  refine ⟨h, hlow, ?_, ?_, ?_⟩
  · -- injectivity on `Iio β`
    have key : ∀ γ₁ ∈ Set.Iio β, ∀ γ₂ ∈ Set.Iio β, γ₁ < α → ¬ γ₂ < α → h γ₁ ≠ h γ₂ := by
      intro γ₁ h₁ γ₂ h₂ hγ₁ hγ₂ heq
      rw [hlow γ₁ hγ₁] at heq
      by_cases hE₂ : γ₂ ∈ E
      · rw [hmid γ₂ hE₂ hγ₂] at heq
        exact (hSnot _ (hrS _ hE₂)).2.1 ⟨γ₁, hγ₁, heq.symm⟩
      · rw [hhigh γ₂ hγ₂ hE₂] at heq
        by_cases hD₁ : γ₁ ∈ D
        · exact hnotB γ₂ h₂ hγ₂ hE₂ (Or.inl ⟨γ₁, hD₁, heq⟩)
        · have : g γ₁ = fβ γ₁ := by
            by_contra hne
            exact hD₁ ⟨hγ₁, hne⟩
          rw [this] at heq
          have := hinj (Set.mem_Iio.2 (hγ₁.trans_le hαβ)) h₂ heq
          exact absurd (this ▸ hγ₁) hγ₂
    have key2 : ∀ γ₁ ∈ Set.Iio β, ∀ γ₂ ∈ Set.Iio β, γ₁ ∈ E → ¬ γ₁ < α → ¬ γ₂ < α →
        γ₂ ∉ E → h γ₁ ≠ h γ₂ := by
      intro γ₁ _ γ₂ h₂ hE₁ hγ₁ hγ₂ hE₂ heq
      rw [hmid γ₁ hE₁ hγ₁, hhigh γ₂ hγ₂ hE₂] at heq
      exact (hSnot _ (hrS _ hE₁)).1 ⟨γ₂, h₂, heq.symm⟩
    intro γ₁ h₁ γ₂ h₂ heq
    by_cases hγ₁ : γ₁ < α <;> by_cases hγ₂ : γ₂ < α
    · rw [hlow γ₁ hγ₁, hlow γ₂ hγ₂] at heq
      exact hg hγ₁ hγ₂ heq
    · exact absurd heq (key γ₁ h₁ γ₂ h₂ hγ₁ hγ₂)
    · exact absurd heq.symm (key γ₂ h₂ γ₁ h₁ hγ₂ hγ₁)
    · by_cases hE₁ : γ₁ ∈ E <;> by_cases hE₂ : γ₂ ∈ E
      · rw [hmid γ₁ hE₁ hγ₁, hmid γ₂ hE₂ hγ₂] at heq
        exact hrinj hE₁ hE₂ heq
      · exact absurd heq (key2 γ₁ h₁ γ₂ h₂ hE₁ hγ₁ hγ₂ hE₂)
      · exact absurd heq.symm (key2 γ₂ h₂ γ₁ h₁ hE₂ hγ₂ hγ₁ hE₁)
      · rw [hhigh γ₁ hγ₁ hE₁, hhigh γ₂ hγ₂ hE₂] at heq
        exact hinj h₁ h₂ heq
  · -- the difference set is finite
    refine (hdiff.union hEfin).subset ?_
    rintro γ ⟨hγβ, hne⟩
    by_cases hγα : γ < α
    · exact Or.inl ⟨hγα, by rwa [hlow γ hγα] at hne⟩
    · by_cases hγE : γ ∈ E
      · exact Or.inr hγE
      · exact absurd (hhigh γ hγα hγE) hne
  · -- values avoid `R`
    intro γ hγβ
    by_cases hγα : γ < α
    · rw [hlow γ hγα]; exact hgR γ hγα
    · by_cases hγE : γ ∈ E
      · rw [hmid γ hγE hγα]
        exact (hSnot _ (hrS _ hγE)).2.2
      · rw [hhigh γ hγα hγE]
        exact fun hmem => hnotB γ hγβ hγα hγE (Or.inr hmem)

end Aronszajn

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

