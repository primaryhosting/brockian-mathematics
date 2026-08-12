import RequestProject.Main

/-! Sanity checks for `Frontier.aumann_agreement`: the hypotheses are satisfiable by a
concrete example with two genuinely different information partitions. -/

example : (1 : ℝ) = 1 :=
  Frontier.aumann_agreement (Ω := Bool) (fun _ => (1 : ℝ) / 2) Finset.univ
    (fun _ => Finset.univ) (fun ω => {ω})
    (fun _ => Finset.mem_univ _) (fun _ _ _ => rfl)
    (fun _ => Finset.mem_singleton_self _)
    (fun _ _ h => by simp only [Finset.mem_singleton] at h; subst h; rfl)
    Finset.univ (fun _ _ => Finset.subset_univ _) (fun _ _ => Finset.subset_univ _)
    (by norm_num [Frontier.prob, Fintype.sum_bool]) 1 1
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])
    (fun _ _ => by norm_num [Frontier.prob, Fintype.sum_bool])

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

namespace Frontier

/-- The prior probability (mass) that the common prior `p` assigns to a finite event `s`. -/
noncomputable def prob {Ω : Type*} (p : Ω → ℝ) (s : Finset Ω) : ℝ := ∑ x ∈ s, p x

@[simp] lemma prob_empty {Ω : Type*} (p : Ω → ℝ) : prob p (∅ : Finset Ω) = 0 := by
  simp [prob]

/-- If an event `C` is a union of cells of an information partition `I`, and the posterior
probability of `E` is the constant `q` on every cell of `I` inside `C`, then the posterior
probability of `E` given `C` is also `q` (stated multiplicatively). -/
theorem prob_inter_of_posterior_const
    {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (E : Finset Ω) (I : Ω → Finset Ω)
    (hself : ∀ ω, ω ∈ I ω) (hcell : ∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω) (q : ℝ) :
    ∀ C : Finset Ω, (∀ ω ∈ C, I ω ⊆ C) →
      (∀ ω ∈ C, prob p (E ∩ I ω) = q * prob p (I ω)) →
      prob p (E ∩ C) = q * prob p C := by
  intro C
  induction C using Finset.strongInduction with
  | _ C ih =>
    intro hclosed hpost
    rcases C.eq_empty_or_nonempty with rfl | ⟨ω, hω⟩
    · simp
    · have hA : I ω ⊆ C := hclosed ω hω
      have hωA : ω ∈ I ω := hself ω
      have hsub : C \ I ω ⊂ C := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨ω, hω, ?_⟩
        simp [hωA]
      -- disjointness: any cell meeting `I ω` equals `I ω`
      have hdisj : ∀ ω' ∈ C \ I ω, I ω' ⊆ C \ I ω := by
        intro ω' hω'
        rw [Finset.mem_sdiff] at hω'
        intro x hx
        rw [Finset.mem_sdiff]
        refine ⟨hclosed ω' hω'.1 hx, ?_⟩
        intro hxA
        have h1 : I x = I ω' := hcell ω' x hx
        have h2 : I x = I ω := hcell ω x hxA
        have h3 : I ω' = I ω := by rw [← h1, h2]
        exact hω'.2 (h3 ▸ hself ω')
      have hrec := ih (C \ I ω) hsub hdisj
        (fun ω' hω' => hpost ω' (Finset.sdiff_subset hω'))
      have hsum : prob p (C \ I ω) + prob p (I ω) = prob p C := Finset.sum_sdiff hA
      have hEsub : E ∩ I ω ⊆ E ∩ C := Finset.inter_subset_inter_left hA
      have hEeq : (E ∩ C) \ (E ∩ I ω) = E ∩ (C \ I ω) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have hEsum : prob p ((E ∩ C) \ (E ∩ I ω)) + prob p (E ∩ I ω) = prob p (E ∩ C) :=
        Finset.sum_sdiff hEsub
      rw [hEeq] at hEsum
      rw [← hEsum, hrec, hpost ω hω, ← hsum]
      ring

/-- **Aumann's agreement theorem** (finite, base case): two agents with a common prior `p` who
have common knowledge of their posterior probabilities of an event `E` must assign the same
posterior probability to `E`.

Here `I₁`, `I₂` are the agents' information partitions (`hself`/`hcell` say each `I i ω` is the
cell of a partition containing `ω`), and `C` is a common-knowledge event at the state of
interest: it is a union of cells of both partitions. Common knowledge that agent `i`'s posterior
is `qᵢ` says exactly that the posterior is `qᵢ` on every cell of agent `i` inside `C`.
The conclusion is that the two posteriors coincide: the agents cannot agree to disagree. -/
theorem aumann_agreement
    {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (E : Finset Ω) (I₁ I₂ : Ω → Finset Ω)
    (h₁self : ∀ ω, ω ∈ I₁ ω) (h₁cell : ∀ ω ω' : Ω, ω' ∈ I₁ ω → I₁ ω' = I₁ ω)
    (h₂self : ∀ ω, ω ∈ I₂ ω) (h₂cell : ∀ ω ω' : Ω, ω' ∈ I₂ ω → I₂ ω' = I₂ ω)
    (C : Finset Ω) (hC₁ : ∀ ω ∈ C, I₁ ω ⊆ C) (hC₂ : ∀ ω ∈ C, I₂ ω ⊆ C)
    (hCpos : 0 < prob p C)
    (q₁ q₂ : ℝ)
    (hcell₁pos : ∀ ω ∈ C, 0 < prob p (I₁ ω)) (hcell₂pos : ∀ ω ∈ C, 0 < prob p (I₂ ω))
    (hpost₁ : ∀ ω ∈ C, prob p (E ∩ I₁ ω) / prob p (I₁ ω) = q₁)
    (hpost₂ : ∀ ω ∈ C, prob p (E ∩ I₂ ω) / prob p (I₂ ω) = q₂) :
    q₁ = q₂ := by
  have key : ∀ (I : Ω → Finset Ω) (q : ℝ), (∀ ω, ω ∈ I ω) →
      (∀ ω ω' : Ω, ω' ∈ I ω → I ω' = I ω) → (∀ ω ∈ C, I ω ⊆ C) →
      (∀ ω ∈ C, 0 < prob p (I ω)) →
      (∀ ω ∈ C, prob p (E ∩ I ω) / prob p (I ω) = q) →
      prob p (E ∩ C) = q * prob p C := by
    intro I q hself hcell hclosed hposcell hpost
    refine prob_inter_of_posterior_const p E I hself hcell q C hclosed ?_
    intro ω hω
    exact (div_eq_iff (ne_of_gt (hposcell ω hω))).1 (hpost ω hω)
  have e₁ := key I₁ q₁ h₁self h₁cell hC₁ hcell₁pos hpost₁
  have e₂ := key I₂ q₂ h₂self h₂cell hC₂ hcell₂pos hpost₂
  have : q₁ * prob p C = q₂ * prob p C := by rw [← e₁, ← e₂]
  exact mul_right_cancel₀ (ne_of_gt hCpos) this

end Frontier

