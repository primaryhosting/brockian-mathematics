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
theorem countable_Iio_iff (a : Ordinal.{0}) : (Set.Iio a).Countable ↔ a < ω₁ := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one,
    ← Cardinal.ord_aleph 1, Cardinal.lt_ord]

theorem countable_Iio {a : Ordinal.{0}} (h : a < ω₁) : (Set.Iio a).Countable :=
  (countable_Iio_iff a).2 h

theorem not_countable_Iio_omega1 : ¬ (Set.Iio (ω₁ : Ordinal.{0})).Countable := by
  rw [countable_Iio_iff]
  exact lt_irrefl _

/-! ### A dependent choice helper -/

/-- Build a sequence by repeated choice, keeping an invariant and a step relation. -/
theorem exists_seq_of_step {σ : Type*} (Inv : ℕ → σ → Prop) (Rel : ℕ → σ → σ → Prop)
    (s₀ : σ) (h₀ : Inv 0 s₀)
    (step : ∀ n s, Inv n s → ∃ s', Inv (n + 1) s' ∧ Rel n s s') :
    ∃ u : ℕ → σ, u 0 = s₀ ∧ (∀ n, Inv n (u n)) ∧ ∀ n, Rel n (u n) (u (n + 1)) := by
  classical
  let F : ∀ n : ℕ, {s : σ // Inv n s} := fun n =>
    Nat.rec (motive := fun n => {s : σ // Inv n s}) ⟨s₀, h₀⟩
      (fun n ih => ⟨(step n ih.1 ih.2).choose, (step n ih.1 ih.2).choose_spec.1⟩) n
  exact ⟨fun n => (F n).1, rfl, fun n => (F n).2,
    fun n => (step n (F n).1 (F n).2).choose_spec.2⟩

/-! ### Difference sets -/

/-- The set of `γ < α` on which `f` and `g` differ. -/
def diffSet (α : Ordinal.{0}) (f g : Ordinal.{0} → ℕ) : Set Ordinal.{0} :=
  {γ | γ < α ∧ f γ ≠ g γ}

theorem diffSet_comm (α : Ordinal.{0}) (f g : Ordinal.{0} → ℕ) :
    diffSet α f g = diffSet α g f := by
  ext γ; simp only [diffSet, mem_setOf_eq, ne_eq, eq_comm]

theorem diffSet_mono {α β : Ordinal.{0}} (h : α ≤ β) (f g : Ordinal.{0} → ℕ) :
    diffSet α f g ⊆ diffSet β f g := fun _ hγ => ⟨hγ.1.trans_le h, hγ.2⟩

theorem diffSet_trans (α : Ordinal.{0}) (f g h : Ordinal.{0} → ℕ) :
    diffSet α f h ⊆ diffSet α f g ∪ diffSet α g h := by
  rintro γ ⟨hγ, hne⟩
  by_cases hfg : f γ = g γ
  · exact Or.inr ⟨hγ, by rw [← hfg]; exact hne⟩
  · exact Or.inl ⟨hγ, hfg⟩

theorem diffSet_self (α : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : diffSet α f f = ∅ := by
  ext γ; simp [diffSet]

/-- `CoInf α f` says that the range of `f` on `Iio α` misses infinitely many naturals. -/
def CoInf (α : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop := ((f '' Set.Iio α)ᶜ).Infinite

theorem image_subset_of_diffSet (α : Ordinal.{0}) (f g : Ordinal.{0} → ℕ) :
    g '' Set.Iio α ⊆ f '' Set.Iio α ∪ g '' (diffSet α f g) := by
  rintro n ⟨γ, hγ, rfl⟩
  by_cases h : f γ = g γ
  · exact Or.inl ⟨γ, hγ, h⟩
  · exact Or.inr ⟨γ, ⟨hγ, h⟩, rfl⟩

theorem CoInf.of_diffSet_finite {α : Ordinal.{0}} {f g : Ordinal.{0} → ℕ} (hf : CoInf α f)
    (hd : (diffSet α f g).Finite) : CoInf α g := by
  have hsub : ((f '' Set.Iio α)ᶜ \ (g '' (diffSet α f g))) ⊆ (g '' Set.Iio α)ᶜ := by
    intro n hn
    intro hmem
    rcases image_subset_of_diffSet α f g hmem with h | h
    · exact hn.1 h
    · exact hn.2 h
  exact (hf.diff (hd.image g)).mono hsub

/-! ### The extension lemma -/

/-- Given a finite set `E` of ordinals and an infinite set `S ⊆ ℕ`, there is a function
which is injective on `E` with all values on `E` lying in `S`. -/
theorem exists_injOn_into_infinite {E : Set Ordinal.{0}} (hE : E.Finite) {S : Set ℕ}
    (hS : S.Infinite) : ∃ r : Ordinal.{0} → ℕ, Set.InjOn r E ∧ ∀ γ ∈ E, r γ ∈ S := by
  classical
  have : Fintype E := hE.fintype
  obtain ⟨j, hj⟩ : ∃ j : E → ℕ, Function.Injective j :=
    ⟨fun x => (Fintype.equivFin E x : ℕ), fun a b hab => by
      simpa using Fin.val_injective (α := fun _ => True) (by simpa using hab)⟩
  let emb : ℕ ↪ S := hS.natEmbedding S
  refine ⟨fun γ => if h : γ ∈ E then (emb (j ⟨γ, h⟩) : ℕ) else 0, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [dif_pos ha, dif_pos hb] at hab
    have : emb (j ⟨a, ha⟩) = emb (j ⟨b, hb⟩) := Subtype.ext hab
    have := hj (emb.injective this)
    exact congrArg Subtype.val this
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (emb (j ⟨γ, hγ⟩)).2

/-- **Extension lemma.**  Suppose `fβ` is injective on `Iio β` with co-infinite range, and
`g` is injective on `Iio α` (`α ≤ β`), differs from `fβ` on only finitely many points below
`α`, and avoids the finite set `R`.  Then `g` extends to a function on `Iio β` with the same
properties relative to `β`. -/
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

