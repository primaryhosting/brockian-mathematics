/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Set Function

namespace Frontier

/-! ## Finite games in normal form

A finite game in normal form consists of a finite set of players `I`, for each player a finite
nonempty set of pure strategies `S i`, and a payoff function `u i : (∀ j, S j) → ℝ`.

A *mixed strategy* for player `i` is an element of `stdSimplex ℝ (S i)`, and a *mixed strategy
profile* is an element of the product of these simplices. -/

section Game

variable {I : Type} [Fintype I] [DecidableEq I]
  (S : I → Type) [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  (u : I → (∀ i, S i) → ℝ)

/-- The set of mixed strategy profiles of a finite game. -/
def profiles : Set (∀ i, S i → ℝ) := Set.pi Set.univ fun i => stdSimplex ℝ (S i)

/-- The expected payoff to player `k` of the mixed strategy profile `x`. -/
noncomputable def expectedPayoff (x : ∀ i, S i → ℝ) (k : I) : ℝ :=
  ∑ p : (∀ i, S i), (∏ j, x j (p j)) * u k p

/-- `x` is a (mixed strategy) Nash equilibrium: it is a mixed strategy profile, and no player
can strictly increase their expected payoff by unilaterally deviating to another mixed
strategy. -/
def IsNashEquilibrium (x : ∀ i, S i → ℝ) : Prop :=
  x ∈ profiles S ∧
    ∀ (i : I) (y : S i → ℝ), y ∈ stdSimplex ℝ (S i) →
      expectedPayoff S u (Function.update x i y) i ≤ expectedPayoff S u x i

end Game

/-- Brouwer's fixed point theorem, as a statement about all nonempty compact convex subsets of
finite-dimensional real normed spaces. -/
def BrouwerFixedPointProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Proof

variable {I : Type} [Fintype I] [DecidableEq I]
  {S : I → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  (u : I → (∀ i, S i) → ℝ)

/-! ### Basic properties of the set of profiles -/

omit [Fintype I] [DecidableEq I] in
/-- The set of mixed strategy profiles is nonempty. -/
theorem profiles_nonempty [∀ i, Nonempty (S i)] : (profiles S).Nonempty :=
  ⟨fun i => Pi.single (Classical.arbitrary (S i)) 1,
    fun i _ => single_mem_stdSimplex ℝ (Classical.arbitrary (S i))⟩

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem profiles_convex : Convex ℝ (profiles S) :=
  convex_pi fun i _ => convex_stdSimplex ℝ (S i)

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (S i)] in
theorem profiles_isCompact : IsCompact (profiles S) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex (S i)

/-! ### Multilinearity of the expected payoff -/

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem prod_update_eq (x : ∀ i, S i → ℝ) (i : I) (z : S i → ℝ) (p : ∀ i, S i) :
    ∏ j, (Function.update x i z) j (p j)
      = z (p i) * ∏ j ∈ Finset.univ.erase i, x j (p j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (Function.update x i z) j (p j))
    (Finset.mem_univ i), Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The expected payoff is affine (indeed linear) in the mixed strategy of any single player:
deviating to the mixed strategy `y` gives the `y`-average of the payoffs obtained by deviating
to the pure strategies. -/
theorem expectedPayoff_update_eq_sum (x : ∀ i, S i → ℝ) (i k : I) (y : S i → ℝ) :
    expectedPayoff S u (Function.update x i y) k
      = ∑ s : S i, y s * expectedPayoff S u (Function.update x i (Pi.single s 1)) k := by
  simp only [expectedPayoff, prod_update_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- Specialisation of `expectedPayoff_update_eq_sum` to `y = x i`, i.e. no deviation at all. -/
theorem expectedPayoff_eq_sum (x : ∀ i, S i → ℝ) (i k : I) :
    expectedPayoff S u x k
      = ∑ s : S i, x i s * expectedPayoff S u (Function.update x i (Pi.single s 1)) k := by
  conv_lhs => rw [← Function.update_eq_self i x]
  exact expectedPayoff_update_eq_sum u x i k (x i)

/-! ### Continuity -/

omit [∀ i, DecidableEq (S i)] in
theorem continuous_expectedPayoff (k : I) :
    Continuous fun x : (∀ i, S i → ℝ) => expectedPayoff S u x k := by
  unfold expectedPayoff; fun_prop

omit [Fintype I] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
theorem continuous_update (i : I) (y : S i → ℝ) :
    Continuous fun x : (∀ i, S i → ℝ) => Function.update x i y := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h; simpa only [Function.update_self] using continuous_const
  · simpa only [Function.update_of_ne h] using continuous_apply j

omit [∀ i, DecidableEq (S i)] in
theorem continuous_update_expectedPayoff (i k : I) (y : S i → ℝ) :
    Continuous fun x : (∀ i, S i → ℝ) => expectedPayoff S u (Function.update x i y) k :=
  (continuous_expectedPayoff u k).comp (continuous_update i y)

/-! ### Nash's map -/

/-- The excess payoff player `i` would get by switching to the pure strategy `s`
(truncated below at `0`). -/
noncomputable def gain (x : ∀ i, S i → ℝ) (i : I) (s : S i) : ℝ :=
  max 0 (expectedPayoff S u (Function.update x i (Pi.single s 1)) i - expectedPayoff S u x i)

theorem gain_nonneg (x : ∀ i, S i → ℝ) (i : I) (s : S i) : 0 ≤ gain u x i s :=
  le_max_left _ _

theorem one_le_gain_denom (x : ∀ i, S i → ℝ) (i : I) :
    (1 : ℝ) ≤ 1 + ∑ t : S i, gain u x i t := by
  have : (0 : ℝ) ≤ ∑ t : S i, gain u x i t :=
    Finset.sum_nonneg fun t _ => gain_nonneg u x i t
  linarith

theorem gain_denom_pos (x : ∀ i, S i → ℝ) (i : I) :
    (0 : ℝ) < 1 + ∑ t : S i, gain u x i t :=
  lt_of_lt_of_le zero_lt_one (one_le_gain_denom u x i)

/-- Nash's map: each player shifts weight towards the pure strategies that would improve
their payoff, and renormalises. -/
noncomputable def nashMap (x : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i s => (x i s + gain u x i s) / (1 + ∑ t : S i, gain u x i t)

theorem continuous_gain (i : I) (s : S i) : Continuous fun x : (∀ i, S i → ℝ) => gain u x i s :=
  continuous_const.max
    ((continuous_update_expectedPayoff u i i _).sub (continuous_expectedPayoff u i))

theorem continuous_nashMap : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  have hcoord : Continuous fun x : (∀ i, S i → ℝ) => x i s :=
    (continuous_apply s).comp (continuous_apply i)
  exact Continuous.div (hcoord.add (continuous_gain u i s))
    (continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain u i t))
    fun x => ne_of_gt (gain_denom_pos u x i)

theorem nashMap_mapsTo : Set.MapsTo (nashMap u) (profiles S) (profiles S) := by
  intro x hx i _
  have hxi := hx i (Set.mem_univ i)
  refine ⟨fun s => ?_, ?_⟩
  · exact div_nonneg (add_nonneg (hxi.1 s) (gain_nonneg u x i s)) (gain_denom_pos u x i).le
  · rw [show (∑ s : S i, nashMap u x i s)
        = (∑ s : S i, (x i s + gain u x i s)) / (1 + ∑ t : S i, gain u x i t) by
      rw [Finset.sum_div]; rfl]
    rw [Finset.sum_add_distrib, hxi.2]
    exact div_self (ne_of_gt (gain_denom_pos u x i))

/-! ### From a fixed point to a Nash equilibrium -/

/-- At a fixed point of Nash's map, no pure deviation is profitable. -/
theorem gain_eq_zero_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ profiles S)
    (hfix : nashMap u x = x) (i : I) (s : S i) : gain u x i s = 0 := by
  have hxi := hx i (Set.mem_univ i)
  set D : ℝ := ∑ t : S i, gain u x i t with hD
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun t _ => gain_nonneg u x i t
  have hpos : (0 : ℝ) < 1 + D := gain_denom_pos u x i
  -- the fixed point equation, rearranged
  have key : ∀ t : S i, gain u x i t = x i t * D := by
    intro t
    have h := congrFun (congrFun hfix i) t
    rw [nashMap, div_eq_iff (ne_of_gt hpos)] at h
    nlinarith [h]
  -- if the total gain were positive, some strategy in the support would be a strict
  -- improvement over the equilibrium payoff, which is impossible
  have hD0 : D = 0 := by
    by_contra hne
    have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hne)
    set V := expectedPayoff S u x i with hV
    set A : S i → ℝ := fun t => expectedPayoff S u (Function.update x i (Pi.single t 1)) i
      with hA
    have hsum : V = ∑ t : S i, x i t * A t := expectedPayoff_eq_sum u x i i
    -- there is a strategy in the support of `x i` which is not strictly better than `V`
    have hex : ∃ t : S i, 0 < x i t ∧ A t ≤ V := by
      by_contra hcon
      push_neg at hcon
      have hlt : ∑ t : S i, x i t * V < ∑ t : S i, x i t * A t := by
        refine Finset.sum_lt_sum (fun t _ => ?_) ?_
        · rcases eq_or_lt_of_le (hxi.1 t) with h | h
          · simp [← h]
          · exact le_of_lt (by have := hcon t h; nlinarith)
        · -- some strategy has positive weight, since the weights sum to `1`
          obtain ⟨t, -, ht⟩ : ∃ t ∈ Finset.univ, 0 < x i t := by
            by_contra hall
            push_neg at hall
            have : ∑ t : S i, x i t = 0 :=
              Finset.sum_eq_zero fun t ht => le_antisymm (hall t ht) (hxi.1 t)
            rw [hxi.2] at this; exact one_ne_zero this
          exact ⟨t, Finset.mem_univ t, by have := hcon t ht; nlinarith⟩
      rw [← Finset.sum_mul, hxi.2, one_mul, ← hsum] at hlt
      exact lt_irrefl V hlt
    obtain ⟨t, ht, hAt⟩ := hex
    have hAt' : expectedPayoff S u (Function.update x i (Pi.single t 1)) i
        ≤ expectedPayoff S u x i := hAt
    have hzero : gain u x i t = 0 := max_eq_left (by linarith)
    rw [key t] at hzero
    nlinarith
  rw [key s, hD0, mul_zero]

/-- A fixed point of Nash's map inside the set of profiles is a Nash equilibrium. -/
theorem isNashEquilibrium_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ profiles S)
    (hfix : nashMap u x = x) : IsNashEquilibrium S u x := by
  refine ⟨hx, fun i y hy => ?_⟩
  have hle : ∀ s : S i,
      expectedPayoff S u (Function.update x i (Pi.single s 1)) i ≤ expectedPayoff S u x i := by
    intro s
    have h := gain_eq_zero_of_fixed u hx hfix i s
    simp only [gain] at h
    have h1 := max_le_iff.mp (le_of_eq h)
    linarith [h1.2]
  rw [expectedPayoff_update_eq_sum u x i i y]
  calc ∑ s : S i, y s * expectedPayoff S u (Function.update x i (Pi.single s 1)) i
      ≤ ∑ s : S i, y s * expectedPayoff S u x i :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hle s) (hy.1 s)
    _ = expectedPayoff S u x i := by rw [← Finset.sum_mul, hy.2, one_mul]

end Proof

/-- **Nash's theorem**: every finite game in normal form has a mixed strategy Nash equilibrium.

This is stated as a Lean-checked reduction to Brouwer's fixed point theorem (`hB`), which is
not currently available in Mathlib. -/
theorem nash_equilibrium_exists (hB : BrouwerFixedPointProperty)
    {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : I → (∀ i, S i) → ℝ) :
    ∃ x : ∀ i, S i → ℝ, IsNashEquilibrium S u x := by
  obtain ⟨x, hx, hfix⟩ :=
    hB (∀ i, S i → ℝ) (profiles S) profiles_nonempty profiles_isCompact profiles_convex
      (nashMap u) (continuous_nashMap u).continuousOn (nashMap_mapsTo u)
  exact ⟨x, isNashEquilibrium_of_fixed u hx hfix⟩

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

