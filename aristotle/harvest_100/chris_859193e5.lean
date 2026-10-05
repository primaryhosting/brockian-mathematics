/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-!
## Finite games in mixed strategies

A finite game consists of a finite set of players `ι`, a finite nonempty set of pure
strategies `S i` for each player `i`, and a payoff function
`u : ι → (∀ j, S j) → ℝ`.

A *mixed strategy* for player `i` is a probability vector on `S i`, i.e. a function
`x : S i → ℝ` with nonnegative entries summing to `1`.  A *mixed strategy profile*
assigns a mixed strategy to every player, and the expected payoff of player `i` is
the multilinear expression `∑ p, (∏ j, σ j (p j)) * u i p`.
-/

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The mixed strategy concentrated on the pure strategy `s`. -/
def pureStrat {i : ι} (s : S i) : S i → ℝ := fun t => if t = s then 1 else 0

/-- `x` is a mixed strategy: a probability vector on the pure strategies. -/
def IsMixed {i : ι} (x : S i → ℝ) : Prop := (∀ s, 0 ≤ x s) ∧ ∑ s, x s = 1

/-- `σ` is a mixed strategy profile. -/
def IsMixedProfile (σ : ∀ j, S j → ℝ) : Prop := ∀ i, IsMixed (σ i)

/-- The expected payoff of player `i` under the mixed strategy profile `σ`. -/
noncomputable def payoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (σ : ∀ j, S j → ℝ) : ℝ :=
  ∑ p : (∀ j, S j), (∏ j, σ j (p j)) * u i p

/-- `σ` is a Nash equilibrium: it is a mixed strategy profile, and no player can
strictly increase their expected payoff by unilaterally switching to another mixed
strategy. -/
def IsNashEquilibrium (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) : Prop :=
  IsMixedProfile σ ∧
    ∀ (i : ι) (τ : S i → ℝ), IsMixed τ →
      payoff u i (Function.update σ i τ) ≤ payoff u i σ

end Defs

/-- **Brouwer's fixed point theorem**, stated as a property of the ambient set-up:
every continuous self-map of a nonempty compact convex subset of a finite-dimensional
real normed space has a fixed point.

This classical theorem is not (yet) available in Mathlib, so the main theorem below is
stated as a *reduction*: it derives the existence of Nash equilibria from this
hypothesis. -/
def BrouwerFixedPointProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Basic

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  {u : ι → (∀ j, S j) → ℝ}

lemma continuous_eval (j : ι) (s : S j) :
    Continuous fun σ : ∀ k, S k → ℝ => σ j s :=
  (continuous_apply s).comp (continuous_apply j)

lemma isMixed_pureStrat {i : ι} (s : S i) : IsMixed (pureStrat s) := by
  constructor
  · intro t
    by_cases h : t = s <;> simp [pureStrat, h]
  · simp [pureStrat]

lemma prod_update_apply (σ : ∀ j, S j → ℝ) (i : ι) (τ : S i → ℝ) (p : ∀ j, S j) :
    (∏ j, Function.update σ i τ j (p j))
      = τ (p i) * ∏ j ∈ Finset.univ.erase i, σ j (p j) := by
  rw [← Finset.mul_prod_erase (Finset.univ)
      (fun j => Function.update σ i τ j (p j)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Expected payoff is affine in the player's own mixed strategy: it is the
`τ`-average of the payoffs of the pure deviations. -/
lemma payoff_update_eq_sum (u : ι → (∀ j, S j) → ℝ) (i : ι) (σ : ∀ j, S j → ℝ)
    (τ : S i → ℝ) :
    payoff u i (Function.update σ i τ)
      = ∑ s, τ s * payoff u i (Function.update σ i (pureStrat s)) := by
  simp only [payoff, prod_update_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single_of_mem (p i) (Finset.mem_univ _)]
  · rw [show pureStrat (p i) (p i) = 1 from by simp [pureStrat]]
    ring
  · intro s _ hs
    have hne : p i ≠ s := fun h => hs h.symm
    simp [pureStrat, hne]

lemma payoff_eq_sum_pure (u : ι → (∀ j, S j) → ℝ) (i : ι) (σ : ∀ j, S j → ℝ) :
    payoff u i σ = ∑ s, σ i s * payoff u i (Function.update σ i (pureStrat s)) := by
  conv_lhs => rw [← Function.update_eq_self i σ]
  rw [payoff_update_eq_sum]

/-- If no pure deviation is profitable, then no mixed deviation is profitable. -/
lemma le_payoff_of_pure {u : ι → (∀ j, S j) → ℝ} {i : ι} {σ : ∀ j, S j → ℝ}
    (h : ∀ s, payoff u i (Function.update σ i (pureStrat s)) ≤ payoff u i σ)
    (τ : S i → ℝ) (hτ : IsMixed τ) :
    payoff u i (Function.update σ i τ) ≤ payoff u i σ := by
  rw [payoff_update_eq_sum]
  calc ∑ s, τ s * payoff u i (Function.update σ i (pureStrat s))
      ≤ ∑ _s : S i, τ _s * payoff u i σ := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (h s) (hτ.1 s)
    _ = payoff u i σ := by rw [← Finset.sum_mul, hτ.2, one_mul]

/-- Some pure strategy in the support of `σ i` is not better than `σ i` itself. -/
lemma exists_support_le {u : ι → (∀ j, S j) → ℝ} {i : ι} {σ : ∀ j, S j → ℝ}
    (hσ : IsMixed (σ i)) :
    ∃ s, 0 < σ i s ∧ payoff u i (Function.update σ i (pureStrat s)) ≤ payoff u i σ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s0, -, hs0⟩ : ∃ s0 ∈ Finset.univ, 0 < σ i s0 := by
    by_contra h
    push_neg at h
    have : ∑ s, σ i s ≤ 0 :=
      Finset.sum_nonpos fun s hs => h s hs
    rw [hσ.2] at this
    linarith
  have hlt : ∑ s, σ i s * payoff u i σ
      < ∑ s, σ i s * payoff u i (Function.update σ i (pureStrat s)) := by
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ s0, ?_⟩
    · rcases lt_or_eq_of_le (hσ.1 s) with hpos | hzero
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hcon s hpos)) (le_of_lt hpos)
      · rw [← hzero]; simp
    · exact mul_lt_mul_of_pos_left (hcon s0 hs0) hs0
  rw [← Finset.sum_mul, hσ.2, one_mul, ← payoff_eq_sum_pure] at hlt
  exact lt_irrefl _ hlt

end Basic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- The set of mixed strategy profiles, as a subset of the finite-dimensional space
`∀ j, S j → ℝ`. -/
def mixedProfiles (ι : Type) [Fintype ι] (S : ι → Type) [∀ i, Fintype (S i)] :
    Set (∀ j, S j → ℝ) := {σ | IsMixedProfile σ}

lemma mixedProfiles_nonempty : (mixedProfiles ι S).Nonempty :=
  ⟨fun j => pureStrat (Classical.arbitrary (S j)), fun i => isMixed_pureStrat _⟩

lemma mixedProfiles_convex : Convex ℝ (mixedProfiles ι S) := by
  intro x hx y hy a b ha hb hab i
  refine ⟨fun s => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := (hx i).1 s
    have h2 := (hy i).1 s
    nlinarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hx i).2, (hy i).2,
      mul_one, mul_one, hab]

lemma mixedProfiles_isCompact : IsCompact (mixedProfiles ι S) := by
  have hclosed : IsClosed (mixedProfiles ι S) := by
    have hset : mixedProfiles ι S =
        (⋂ i, ⋂ s : S i, {σ : ∀ j, S j → ℝ | 0 ≤ σ i s})
          ∩ (⋂ i, {σ : ∀ j, S j → ℝ | ∑ s, σ i s = 1}) := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, mixedProfiles,
        IsMixedProfile, IsMixed]
      constructor
      · intro h
        exact ⟨fun i s => (h i).1 s, fun i => (h i).2⟩
      · rintro ⟨h1, h2⟩ i
        exact ⟨fun s => h1 i s, h2 i⟩
    rw [hset]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun s => ?_)
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const (continuous_eval i s)
    · exact isClosed_eq (continuous_finset_sum _ fun s _ => continuous_eval i s)
        continuous_const
  have hbdd : Bornology.IsBounded (mixedProfiles ι S) := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ∀ j, S j → ℝ)) (r := 1)) ?_
    intro σ hσ
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro s
    rw [Real.norm_eq_abs, abs_le]
    have hle : σ j s ≤ ∑ t, σ j t :=
      Finset.single_le_sum (fun t _ => (hσ j).1 t) (Finset.mem_univ s)
    rw [(hσ j).2] at hle
    exact ⟨by linarith [(hσ j).1 s], hle⟩
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

/-- Nash's regret function: the (nonnegative) gain player `i` would get by switching
to the pure strategy `s`. -/
noncomputable def gain (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) (σ : ∀ j, S j → ℝ) : ℝ :=
  max 0 (payoff u i (Function.update σ i (pureStrat s)) - payoff u i σ)

/-- Nash's map: reweight each strategy by its regret and renormalize. -/
noncomputable def nashMap (u : ι → (∀ j, S j) → ℝ) (σ : ∀ j, S j → ℝ) : ∀ j, S j → ℝ :=
  fun i s => (σ i s + gain u i s σ) / (1 + ∑ t, gain u i t σ)

variable {u : ι → (∀ j, S j) → ℝ}

lemma gain_nonneg (i : ι) (s : S i) (σ : ∀ j, S j → ℝ) : 0 ≤ gain u i s σ :=
  le_max_left _ _

lemma one_le_one_add_sum_gain (i : ι) (σ : ∀ j, S j → ℝ) :
    (1 : ℝ) ≤ 1 + ∑ t, gain u i t σ := by
  have : (0 : ℝ) ≤ ∑ t, gain u i t σ :=
    Finset.sum_nonneg fun t _ => gain_nonneg i t σ
  linarith

lemma continuous_payoff (i : ι) : Continuous (fun σ : ∀ j, S j → ℝ => payoff u i σ) := by
  refine continuous_finset_sum _ fun p _ => ?_
  exact (continuous_finset_prod _ fun j _ => continuous_eval j (p j)).mul
    continuous_const

lemma continuous_payoff_update (i : ι) (τ : S i → ℝ) :
    Continuous (fun σ : ∀ j, S j → ℝ => payoff u i (Function.update σ i τ)) := by
  simp only [payoff, prod_update_apply]
  refine continuous_finset_sum _ fun p _ => ?_
  exact ((continuous_const.mul
    (continuous_finset_prod _ fun j _ => continuous_eval j (p j))).mul continuous_const)

lemma continuous_nashMap : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  have hg : ∀ t : S i, Continuous (fun σ : ∀ j, S j → ℝ => gain u i t σ) := fun t =>
    continuous_const.max ((continuous_payoff_update i (pureStrat t)).sub (continuous_payoff i))
  refine Continuous.div ((continuous_eval i s).add (hg s))
    (continuous_const.add (continuous_finset_sum _ fun t _ => hg t)) ?_
  intro σ
  have := one_le_one_add_sum_gain (u := u) i σ
  intro h
  rw [h] at this
  linarith

lemma nashMap_mapsTo : Set.MapsTo (nashMap u) (mixedProfiles ι S) (mixedProfiles ι S) := by
  intro σ hσ i
  have hD : (0 : ℝ) < 1 + ∑ t, gain u i t σ :=
    lt_of_lt_of_le zero_lt_one (one_le_one_add_sum_gain i σ)
  refine ⟨fun s => ?_, ?_⟩
  · exact div_nonneg (add_nonneg ((hσ i).1 s) (gain_nonneg i s σ)) hD.le
  · show ∑ s, (σ i s + gain u i s σ) / (1 + ∑ t, gain u i t σ) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, (hσ i).2]
    field_simp

lemma isNashEquilibrium_of_fixed {σ : ∀ j, S j → ℝ} (hσ : IsMixedProfile σ)
    (hfix : nashMap u σ = σ) : IsNashEquilibrium u σ := by
  refine ⟨hσ, fun i τ hτ => le_payoff_of_pure ?_ τ hτ⟩
  have hD : (0 : ℝ) < 1 + ∑ t, gain u i t σ :=
    lt_of_lt_of_le zero_lt_one (one_le_one_add_sum_gain i σ)
  have hfixs : ∀ t : S i, (σ i t + gain u i t σ) / (1 + ∑ r, gain u i r σ) = σ i t :=
    fun t => congrFun (congrFun hfix i) t
  have key : ∀ t : S i, gain u i t σ = σ i t * ∑ r, gain u i r σ := by
    intro t
    have h := hfixs t
    rw [div_eq_iff (ne_of_gt hD)] at h
    nlinarith [h]
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_le (u := u) (i := i) (σ := σ) (hσ i)
  have h0 : gain u i s0 σ = 0 := by
    rw [gain, max_eq_left (by linarith)]
  have hGzero : ∑ r, gain u i r σ = 0 := by
    have := key s0
    rw [h0] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h (ne_of_gt hs0pos)
    · exact h
  intro s
  have hs : gain u i s σ = 0 := by rw [key s, hGzero, mul_zero]
  rw [gain] at hs
  have := max_eq_left_iff.1 hs
  linarith

/-- **Nash's theorem**: every finite game has a mixed-strategy Nash equilibrium.

The proof is Nash's classical argument, reducing the statement to Brouwer's fixed
point theorem (`BrouwerFixedPointProperty`), which is supplied as a hypothesis since
it is not available in Mathlib. -/
theorem nash_equilibrium_exists (hB : BrouwerFixedPointProperty)
    (u : ι → (∀ j, S j) → ℝ) : ∃ σ : ∀ j, S j → ℝ, IsNashEquilibrium u σ := by
  obtain ⟨σ, hσK, hfix⟩ := hB (∀ j, S j → ℝ) (mixedProfiles ι S) mixedProfiles_nonempty
    mixedProfiles_isCompact mixedProfiles_convex (nashMap u)
    continuous_nashMap.continuousOn nashMap_mapsTo
  exact ⟨σ, isNashEquilibrium_of_fixed hσK hfix⟩

end Main

end Frontier

