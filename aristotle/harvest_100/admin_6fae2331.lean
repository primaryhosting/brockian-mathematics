import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Set

namespace Frontier

universe u

/-! ## Finite games in mixed strategies

A finite game is given by a finite type of players `I`, a finite nonempty type of pure
strategies `S i` for each player, and a real payoff function
`u : I → ((i : I) → S i) → ℝ`.
-/

variable {I : Type u} [Fintype I] [DecidableEq I]
  {S : I → Type u} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The set of mixed strategy profiles: for each player, a probability distribution on
that player's pure strategies. -/
def mixedProfiles (S : I → Type u) [Fintype I] [∀ i, Fintype (S i)] :
    Set ((i : I) → S i → ℝ) :=
  Set.univ.pi fun i => stdSimplex ℝ (S i)

/-- The mixed strategy that plays the pure strategy `a` with probability one. -/
def pureMix {i : I} (a : S i) : S i → ℝ := fun b => if b = a then 1 else 0

/-- The expected payoff of player `i` under the mixed profile `σ`. -/
def payoff (u : I → ((i : I) → S i) → ℝ) (i : I) (σ : (i : I) → S i → ℝ) : ℝ :=
  ∑ s : ((i : I) → S i), (∏ j, σ j (s j)) * u i s

/-- The expected payoff of player `i` when they deviate to the pure strategy `a`. -/
def dev (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i) (σ : (i : I) → S i → ℝ) : ℝ :=
  payoff u i (Function.update σ i (pureMix a))

/-- `σ` is a Nash equilibrium: no player can improve their expected payoff by
unilaterally switching to another mixed strategy. -/
def IsNashEquilibrium (u : I → ((i : I) → S i) → ℝ) (σ : (i : I) → S i → ℝ) : Prop :=
  ∀ i : I, ∀ τ ∈ stdSimplex ℝ (S i), payoff u i (Function.update σ i τ) ≤ payoff u i σ

/-! ## Brouwer's fixed point theorem, as a hypothesis

Brouwer's fixed point theorem is not available in Mathlib, so we state it as an explicit
hypothesis and give a fully Lean-checked reduction of Nash's theorem to it. -/

/-- Brouwer's fixed point theorem for nonempty compact convex subsets of a
finite-dimensional real normed space. -/
def BrouwerProperty : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (f : E → E), K.Nonempty → IsCompact K → Convex ℝ K →
    ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

/-! ## Multilinearity of the expected payoff -/

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
lemma prod_update_apply (i : I) (c : S i → ℝ) (σ : (i : I) → S i → ℝ)
    (s : (i : I) → S i) :
    ∏ j, (Function.update σ i c) j (s j) = c (s i) * ∏ j ∈ univ.erase i, σ j (s j) := by
  rw [← Finset.mul_prod_erase univ (fun j => (Function.update σ i c) j (s j)) (mem_univ i),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The expected payoff is an average, over player `i`'s pure strategies, of the payoffs
obtained by deviating to those pure strategies. -/
lemma payoff_eq_sum_dev (u : I → ((i : I) → S i) → ℝ) (i : I) (σ : (i : I) → S i → ℝ) :
    payoff u i σ = ∑ a : S i, σ i a * dev u i a σ := by
  simp only [payoff, dev, prod_update_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_prod_erase univ (fun j => σ j (s j)) (mem_univ i)]
  have key : ∀ x : S i,
      σ i x * ((pureMix x (s i) * ∏ j ∈ univ.erase i, σ j (s j)) * u i s)
        = if s i = x then σ i (s i) * ((∏ j ∈ univ.erase i, σ j (s j)) * u i s) else 0 := by
    intro x; by_cases h : s i = x <;> simp [pureMix, h]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_ite_eq]
  simp
  ring

lemma dev_update (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i)
    (σ : (i : I) → S i → ℝ) (τ : S i → ℝ) :
    dev u i a (Function.update σ i τ) = dev u i a σ := by
  simp [dev, Function.update_idem]

lemma payoff_update_eq_sum_dev (u : I → ((i : I) → S i) → ℝ) (i : I)
    (σ : (i : I) → S i → ℝ) (τ : S i → ℝ) :
    payoff u i (Function.update σ i τ) = ∑ a : S i, τ a * dev u i a σ := by
  rw [payoff_eq_sum_dev u i (Function.update σ i τ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Function.update_self, dev_update]

/-- If no pure deviation is profitable then no mixed deviation is either. -/
lemma isNashEquilibrium_of_dev_le (u : I → ((i : I) → S i) → ℝ) (σ : (i : I) → S i → ℝ)
    (h : ∀ i : I, ∀ a : S i, dev u i a σ ≤ payoff u i σ) : IsNashEquilibrium u σ := by
  intro i τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  rw [payoff_update_eq_sum_dev]
  calc ∑ a : S i, τ a * dev u i a σ ≤ ∑ a : S i, τ a * payoff u i σ := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (h i a) (hτ0 a)
    _ = payoff u i σ := by rw [← Finset.sum_mul, hτ1, one_mul]

/-! ## The Nash improvement map -/

/-- The improvement of player `i` from switching to the pure strategy `a`, truncated
below at zero. -/
def gain (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i) (σ : (i : I) → S i → ℝ) : ℝ :=
  max 0 (dev u i a σ - payoff u i σ)

/-- Nash's improvement map. -/
noncomputable def nashMap (u : I → ((i : I) → S i) → ℝ) (σ : (i : I) → S i → ℝ) :
    (i : I) → S i → ℝ :=
  fun i a => (σ i a + gain u i a σ) / (1 + ∑ b : S i, gain u i b σ)

lemma gain_nonneg (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i)
    (σ : (i : I) → S i → ℝ) : 0 ≤ gain u i a σ := le_max_left _ _

lemma one_add_sum_gain_pos (u : I → ((i : I) → S i) → ℝ) (i : I)
    (σ : (i : I) → S i → ℝ) : 0 < 1 + ∑ b : S i, gain u i b σ := by
  have : (0 : ℝ) ≤ ∑ b : S i, gain u i b σ :=
    Finset.sum_nonneg fun b _ => gain_nonneg u i b σ
  linarith

/-! ## Continuity -/

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
lemma continuous_update (i : I) (c : S i → ℝ) :
    Continuous fun σ : (i : I) → S i → ℝ => Function.update σ i c := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa only [Function.update_self] using continuous_const
  · simpa only [Function.update_of_ne h] using continuous_apply j

lemma continuous_payoff (u : I → ((i : I) → S i) → ℝ) (i : I) :
    Continuous fun σ : (i : I) → S i → ℝ => payoff u i σ := by
  refine continuous_finset_sum _ fun s _ => ?_
  refine Continuous.mul ?_ continuous_const
  refine continuous_finset_prod _ fun j _ => ?_
  exact (continuous_apply (s j)).comp (continuous_apply j)

lemma continuous_dev (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i) :
    Continuous fun σ : (i : I) → S i → ℝ => dev u i a σ :=
  (continuous_payoff u i).comp (continuous_update i (pureMix a))

lemma continuous_gain (u : I → ((i : I) → S i) → ℝ) (i : I) (a : S i) :
    Continuous fun σ : (i : I) → S i → ℝ => gain u i a σ :=
  continuous_const.max ((continuous_dev u i a).sub (continuous_payoff u i))

lemma continuous_nashMap (u : I → ((i : I) → S i) → ℝ) :
    Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun a => ?_
  have hcoord : Continuous fun σ : (i : I) → S i → ℝ => σ i a :=
    (continuous_apply a).comp (continuous_apply i)
  exact Continuous.div (hcoord.add (continuous_gain u i a))
    (continuous_const.add (continuous_finset_sum _ fun b _ => continuous_gain u i b))
    fun σ => ne_of_gt (one_add_sum_gain_pos u i σ)

/-! ## Basic properties of the profile space -/

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
lemma mixedProfiles_nonempty [∀ i, Nonempty (S i)] :
    (mixedProfiles S).Nonempty := by
  refine Set.univ_pi_nonempty_iff.mpr fun i => ?_
  exact Nonempty.of_subtype

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
lemma isCompact_mixedProfiles : IsCompact (mixedProfiles S) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex (S i)

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
lemma convex_mixedProfiles : Convex ℝ (mixedProfiles S) :=
  convex_pi fun i _ => convex_stdSimplex ℝ (S i)

omit [DecidableEq I] [∀ i, DecidableEq (S i)] in
lemma mem_mixedProfiles_iff (σ : (i : I) → S i → ℝ) :
    σ ∈ mixedProfiles S ↔ ∀ i, (∀ a, 0 ≤ σ i a) ∧ ∑ a : S i, σ i a = 1 := by
  simp [mixedProfiles, stdSimplex]

lemma mapsTo_nashMap (u : I → ((i : I) → S i) → ℝ) :
    Set.MapsTo (nashMap u) (mixedProfiles S) (mixedProfiles S) := by
  intro σ hσ
  rw [mem_mixedProfiles_iff] at hσ ⊢
  intro i
  obtain ⟨h0, h1⟩ := hσ i
  have hpos := one_add_sum_gain_pos u i σ
  constructor
  · intro a
    exact div_nonneg (add_nonneg (h0 a) (gain_nonneg u i a σ)) hpos.le
  · rw [show (∑ a : S i, nashMap u σ i a)
        = (∑ a : S i, (σ i a + gain u i a σ)) / (1 + ∑ b : S i, gain u i b σ) by
      rw [Finset.sum_div]; rfl]
    rw [Finset.sum_add_distrib, h1]
    exact div_self (ne_of_gt hpos)

/-! ## A fixed point of the Nash map is a Nash equilibrium -/

lemma isNashEquilibrium_of_fixed (u : I → ((i : I) → S i) → ℝ)
    (σ : (i : I) → S i → ℝ) (hσ : σ ∈ mixedProfiles S) (hfix : nashMap u σ = σ) :
    IsNashEquilibrium u σ := by
  rw [mem_mixedProfiles_iff] at hσ
  refine isNashEquilibrium_of_dev_le u σ fun i => ?_
  obtain ⟨h0, h1⟩ := hσ i
  set G : ℝ := ∑ b : S i, gain u i b σ with hG
  have hpos : 0 < 1 + G := one_add_sum_gain_pos u i σ
  -- from the fixed point equation, `gain a = σ i a * G` for every `a`
  have hkey : ∀ a : S i, gain u i a σ = σ i a * G := by
    intro a
    have := congrFun (congrFun hfix i) a
    rw [nashMap, div_eq_iff (ne_of_gt hpos)] at this
    nlinarith [this]
  -- `G` must be zero
  have hG0 : G = 0 := by
    by_contra hne
    have hGpos : 0 < G := lt_of_le_of_ne (Finset.sum_nonneg fun b _ => gain_nonneg u i b σ)
      (Ne.symm hne)
    -- the weighted average of the deviation gains is zero
    have hsum : ∑ a : S i, σ i a * (dev u i a σ - payoff u i σ) = 0 := by
      have := payoff_eq_sum_dev u i σ
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
      linarith [this]
    -- but every term is nonnegative and some term is strictly positive
    have hpos_of : ∀ a : S i, 0 < σ i a → 0 < σ i a * (dev u i a σ - payoff u i σ) := by
      intro a ha
      have hga : 0 < gain u i a σ := by rw [hkey a]; positivity
      rw [gain] at hga
      have hx : 0 < dev u i a σ - payoff u i σ := by
        rcases le_or_gt (dev u i a σ - payoff u i σ) 0 with h | h
        · rw [max_eq_left h] at hga; exact absurd hga (lt_irrefl 0)
        · exact h
      positivity
    have hterm : ∀ a : S i, 0 ≤ σ i a * (dev u i a σ - payoff u i σ) := by
      intro a
      rcases eq_or_lt_of_le (h0 a) with h | h
      · simp [← h]
      · exact (hpos_of a h).le
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : S i, 0 < σ i a₀ := by
      by_contra hc
      push_neg at hc
      have : ∑ a : S i, σ i a = 0 :=
        Finset.sum_eq_zero fun a _ => le_antisymm (hc a) (h0 a)
      rw [h1] at this
      exact one_ne_zero this
    have hsumpos : 0 < ∑ a : S i, σ i a * (dev u i a σ - payoff u i σ) :=
      Finset.sum_pos' (fun a _ => hterm a) ⟨a₀, mem_univ a₀, hpos_of a₀ ha₀⟩
    linarith
  intro a
  have hz : gain u i a σ = 0 := by rw [hkey a, hG0, mul_zero]
  rw [gain] at hz
  by_contra hc
  push_neg at hc
  rw [max_eq_right (by linarith : (0:ℝ) ≤ dev u i a σ - payoff u i σ)] at hz
  linarith

/-! ## Nash's theorem -/

/-- **Nash's theorem**: every finite game has a mixed-strategy Nash equilibrium.

This is a Lean-checked reduction to Brouwer's fixed point theorem (`BrouwerProperty`),
which is not currently available in Mathlib. -/
theorem nash_equilibrium_exists (hB : BrouwerProperty.{u})
    {I : Type u} [Fintype I] [DecidableEq I]
    {S : I → Type u} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : I → ((i : I) → S i) → ℝ) :
    ∃ σ ∈ mixedProfiles S, IsNashEquilibrium u σ := by
  obtain ⟨σ, hσ, hfix⟩ := hB ((i : I) → S i → ℝ) (mixedProfiles S) (nashMap u)
    mixedProfiles_nonempty isCompact_mixedProfiles convex_mixedProfiles
    (continuous_nashMap u).continuousOn (mapsTo_nashMap u)
  exact ⟨σ, hσ, isNashEquilibrium_of_fixed u σ hσ hfix⟩

/-! ## The base case: games with at most one player, unconditionally -/

/-- For a game with at most one player, a Nash equilibrium exists unconditionally. -/
theorem nash_equilibrium_exists_of_subsingleton [Subsingleton I] [∀ i, Nonempty (S i)]
    (u : I → ((i : I) → S i) → ℝ) :
    ∃ σ ∈ mixedProfiles S, IsNashEquilibrium u σ := by
  -- with at most one player, the product over the other players is empty
  have hprod : ∀ (i : I) (σ : (i : I) → S i → ℝ) (s : (i : I) → S i),
      ∏ j ∈ univ.erase i, σ j (s j) = 1 := fun i σ s =>
    Finset.prod_eq_one fun j hj => absurd (Subsingleton.elim j i) (Finset.ne_of_mem_erase hj)
  -- hence the payoff from a pure deviation does not depend on the profile at all
  have hdev : ∀ (i : I) (a : S i) (σ σ' : (i : I) → S i → ℝ),
      dev u i a σ = dev u i a σ' := by
    intro i a σ σ'
    simp only [dev, payoff, prod_update_apply, hprod]
  choose a ha using fun i : I => Finite.exists_max (fun b : S i => dev u i b (fun _ _ => 0))
  refine ⟨fun i => pureMix (a i), ?_, ?_⟩
  · rw [mem_mixedProfiles_iff]
    refine fun i => ⟨fun b => ?_, ?_⟩
    · simp only [pureMix]; positivity
    · simp [pureMix]
  · refine isNashEquilibrium_of_dev_le u _ fun i b => ?_
    rw [payoff_eq_sum_dev, show (∑ c : S i, pureMix (a i) c *
        dev u i c (fun i => pureMix (a i)))
        = dev u i (a i) (fun i => pureMix (a i)) by simp [pureMix]]
    rw [hdev i b _ (fun _ _ => 0), hdev i (a i) _ (fun _ _ => 0)]
    exact ha i b

end Frontier

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

