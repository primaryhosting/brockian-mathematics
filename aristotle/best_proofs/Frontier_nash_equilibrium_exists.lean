import RequestProject.Nash

/-!
# The one-dimensional base case of Brouwer's fixed point theorem

Brouwer's fixed point theorem is not available in Mathlib, and is taken as an explicit
hypothesis in `Frontier.nash_equilibrium_exists`.  Here we prove the one-dimensional base
case of that hypothesis, `BrouwerFixedPointProperty ℝ`, from the intermediate value
theorem; in particular the hypothesis is not vacuous.
-/

open Set

namespace Frontier

/-- **Brouwer's fixed point theorem in dimension one**: every continuous self-map of a
nonempty compact convex subset of `ℝ` has a fixed point. -/
theorem brouwerFixedPointProperty_real : BrouwerFixedPointProperty ℝ := by
  intro K hne hcomp hconv f hf hmaps
  obtain ⟨a, haK, hamin⟩ := hcomp.exists_isLeast hne
  obtain ⟨b, hbK, hbmax⟩ := hcomp.exists_isGreatest hne
  have hKsub : K ⊆ Set.Icc a b := fun x hx => ⟨hamin hx, hbmax hx⟩
  have hIcc : Set.Icc a b ⊆ K := fun x hx => hconv.ordConnected.out haK hbK hx
  have hKeq : K = Set.Icc a b := Set.Subset.antisymm hKsub hIcc
  have hab : a ≤ b := hamin hbK
  have hcont : ContinuousOn (fun x => f x - x) (Set.Icc a b) := by
    rw [← hKeq]
    exact hf.sub continuousOn_id
  have hga : 0 ≤ f a - a := by
    have := hKsub (hmaps haK)
    simp only [Set.mem_Icc] at this
    linarith [this.1]
  have hgb : f b - b ≤ 0 := by
    have := hKsub (hmaps hbK)
    simp only [Set.mem_Icc] at this
    linarith [this.2]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hcont ⟨hgb, hga⟩
  exact ⟨c, hKeq ▸ hc, by linarith [hc0]⟩

end Frontier

import RequestProject.ZeroSum

/-!
# Zero-sum two-player games inside the general framework

The saddle point theorem of `RequestProject.ZeroSum` is transported to the general finite
game framework of `RequestProject.Nash`: a two-player game is one indexed by `Bool`, and a
zero-sum one has `u true = - u false`.  The conclusion is the *unconditional* existence of a
mixed strategy Nash equilibrium in the sense of `Frontier.IsNashEquilibrium`.
-/

open Finset Function Set

namespace Frontier

variable {S : Bool → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- A profile of two players is a pair of strategies. -/
def piBoolEquiv (S : Bool → Type) : (∀ i, S i) ≃ S false × S true where
  toFun p := (p false, p true)
  invFun q := fun i => Bool.rec q.1 q.2 i
  left_inv p := by funext i; cases i <;> rfl
  right_inv q := rfl

/-- The mixed profile of a two-player game determined by the two players' strategies. -/
def pairFun {S : Bool → Type} (x0 : S false → ℝ) (y0 : S true → ℝ) : ∀ i, S i → ℝ :=
  fun i => Bool.rec x0 y0 i

@[simp] theorem pairFun_false {S : Bool → Type} (x0 : S false → ℝ) (y0 : S true → ℝ) :
    pairFun x0 y0 false = x0 := rfl

@[simp] theorem pairFun_true {S : Bool → Type} (x0 : S false → ℝ) (y0 : S true → ℝ) :
    pairFun x0 y0 true = y0 := rfl

/-- The payoff matrix of the row player (player `false`) of a two-player game. -/
def payoffMatrix (u : Bool → (∀ i, S i) → ℝ) (a : S false) (b : S true) : ℝ :=
  u false ((piBoolEquiv S).symm (a, b))

omit [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
theorem expectedPayoff_false (u : Bool → (∀ i, S i) → ℝ) (z : ∀ i, S i → ℝ) :
    expectedPayoff u false z = bilin (payoffMatrix u) (z false) (z true) := by
  rw [expectedPayoff, ← Equiv.sum_comp (piBoolEquiv S).symm
    (fun p => (∏ j, z j (p j)) * u false p), bilin, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.prod_bool]
  have h1 : ((piBoolEquiv S).symm (a, b)) false = a := rfl
  have h2 : ((piBoolEquiv S).symm (a, b)) true = b := rfl
  rw [h1, h2, payoffMatrix]
  ring

omit [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
theorem expectedPayoff_true (u : Bool → (∀ i, S i) → ℝ)
    (hzs : ∀ p, u true p = -u false p) (z : ∀ i, S i → ℝ) :
    expectedPayoff u true z = -bilin (payoffMatrix u) (z false) (z true) := by
  rw [← expectedPayoff_false u z, expectedPayoff, expectedPayoff, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => by rw [hzs p]; ring

/-- Unconditionally (no fixed point theorem needed): every finite two-player zero-sum game
has a mixed strategy Nash equilibrium, in the sense of `Frontier.IsNashEquilibrium`. -/
theorem nash_equilibrium_exists_of_zerosum (u : Bool → (∀ i, S i) → ℝ)
    (hzs : ∀ p, u true p = -u false p) : ∃ x, IsNashEquilibrium u x := by
  obtain ⟨x0, hx0, y0, hy0, hrow, hcol⟩ := exists_saddlePoint (payoffMatrix u)
  refine ⟨pairFun x0 y0, ?_, ?_⟩
  · intro i _
    cases i
    · exact hx0
    · exact hy0
  intro i y hy
  cases i
  · rw [expectedPayoff_false, expectedPayoff_false]
    have h1 : (update (pairFun x0 y0) false y) false = y := update_self _ _ _
    have h2 : (update (pairFun x0 y0) false y) true = y0 := by
      rw [update_of_ne (by decide), pairFun_true]
    rw [h1, h2, pairFun_false, pairFun_true]
    exact hrow y hy
  · rw [expectedPayoff_true _ hzs, expectedPayoff_true _ hzs]
    have h1 : (update (pairFun x0 y0) true y) false = x0 := by
      rw [update_of_ne (by decide), pairFun_false]
    have h2 : (update (pairFun x0 y0) true y) true = y := update_self _ _ _
    rw [h1, h2, pairFun_false, pairFun_true]
    simpa using hcol y hy

end Frontier

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

* `Frontier.IsNashEquilibrium`: mixed strategy Nash equilibrium of a finite game with
  finitely many players, each having a finite nonempty set of pure strategies.
* `Frontier.nash_equilibrium_exists`: **Nash's theorem** — every finite game has a mixed
  strategy Nash equilibrium.  Brouwer's fixed point theorem is not in Mathlib, so it is an
  explicit hypothesis (`BrouwerFixedPointProperty`); the whole of Nash's argument (Nash's
  map, its continuity, that it preserves the product of simplices, and that its fixed
  points are exactly equilibria) is proved here.
* `Frontier.nash_equilibrium_exists_of_potential`: unconditional existence for finite
  potential games.

Companion files prove further unconditional cases: `RequestProject.BrouwerOneDim` (the
one-dimensional case of the Brouwer hypothesis), `RequestProject.ZeroSum` (the minimax
theorem) and `RequestProject.TwoPlayer` (existence for two-player zero-sum games).
-/

open Finset Function Set

namespace Frontier

/-- Brouwer's fixed point theorem, as a property of a real normed space `E`:
every continuous self-map of a nonempty compact convex subset of `E` has a fixed point. -/
def BrouwerFixedPointProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ K : Set E, K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Game

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- The mixed strategy putting all weight on the pure strategy `s`. -/
def dirac {α : Type*} [DecidableEq α] (s : α) : α → ℝ := fun t => if t = s then 1 else 0

/-- The set of mixed strategy profiles of a finite game with players `ι` and
strategy sets `S i`: a tuple of probability distributions, one for each player. -/
def strategyProfiles (S : ι → Type*) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  Set.pi Set.univ fun i => stdSimplex ℝ (S i)

/-- The expected payoff of player `i` under the (independent) mixed profile `x`. -/
noncomputable def expectedPayoff (u : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) : ℝ :=
  ∑ p : ∀ i, S i, (∏ j, x j (p j)) * u i p

/-- `x` is a mixed strategy Nash equilibrium: it is a mixed strategy profile, and no player
can strictly increase their expected payoff by unilaterally switching to another mixed
strategy. -/
def IsNashEquilibrium (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : Prop :=
  x ∈ strategyProfiles S ∧
    ∀ i, ∀ y ∈ stdSimplex ℝ (S i), expectedPayoff u i (update x i y) ≤ expectedPayoff u i x

/-! ### Basic properties of the strategy space -/

theorem dirac_mem_stdSimplex {α : Type*} [Fintype α] [DecidableEq α] (s : α) :
    dirac s ∈ stdSimplex ℝ α := by
  refine ⟨fun t => ?_, ?_⟩
  · simp only [dirac]
    split <;> norm_num
  · simp [dirac]

omit [Fintype ι] [DecidableEq ι] in
theorem strategyProfiles_nonempty : (strategyProfiles S).Nonempty :=
  ⟨fun i => dirac (Classical.arbitrary (S i)), fun _ _ => dirac_mem_stdSimplex _⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
theorem isCompact_strategyProfiles : IsCompact (strategyProfiles S) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex (S i)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
theorem convex_strategyProfiles : Convex ℝ (strategyProfiles S) :=
  convex_pi fun i _ => convex_stdSimplex ℝ (S i)

/-! ### Basic properties of the expected payoff -/

omit [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)] in
theorem continuous_expectedPayoff (u : ι → (∀ i, S i) → ℝ) (i : ι) :
    Continuous (expectedPayoff u i) := by
  refine continuous_finset_sum _ fun p _ => Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun j _ => (continuous_apply (p j)).comp (continuous_apply j)

omit [∀ i, Nonempty (S i)] in
/-- Multilinearity: the expected payoff is the average, over the pure strategies `s` of
player `i`, of the payoffs obtained when player `i` plays `s`. -/
theorem expectedPayoff_eq_sum_pure (u : ι → (∀ i, S i) → ℝ) (i k : ι) (x : ∀ i, S i → ℝ) :
    expectedPayoff u k x = ∑ s : S i, x i s * expectedPayoff u k (update x i (dirac s)) := by
  set F : (∀ j, S j) → ℝ := fun p => ∏ j ∈ univ.erase i, x j (p j)
  have h1 : ∀ p : ∀ j, S j, ∏ j, x j (p j) = x i (p i) * F p := fun p =>
    (Finset.mul_prod_erase univ (fun j => x j (p j)) (mem_univ i)).symm
  have h2 : ∀ (s : S i) (p : ∀ j, S j),
      ∏ j, (update x i (dirac s)) j (p j) = dirac s (p i) * F p := by
    intro s p
    rw [← Finset.mul_prod_erase univ (fun j => (update x i (dirac s)) j (p j)) (mem_univ i),
      update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  have key : ∀ p : ∀ j, S j, ∑ s : S i, x i s * dirac s (p i) = x i (p i) := by
    intro p
    simp [dirac, Finset.sum_ite_eq]
  calc expectedPayoff u k x = ∑ p : ∀ j, S j, x i (p i) * (F p * u k p) := by
        simp only [expectedPayoff, h1, mul_assoc]
    _ = ∑ p : ∀ j, S j, ∑ s : S i, x i s * (dirac s (p i) * (F p * u k p)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← key p, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = ∑ s : S i, ∑ p : ∀ j, S j, x i s * (dirac s (p i) * (F p * u k p)) := Finset.sum_comm
    _ = ∑ s : S i, x i s * expectedPayoff u k (update x i (dirac s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [expectedPayoff, h2, Finset.mul_sum, mul_assoc]

omit [∀ i, Nonempty (S i)] in
/-- If no pure deviation of player `i` beats the value `c`, then no mixed deviation does. -/
theorem expectedPayoff_update_le_of_pure_le (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (x : ∀ i, S i → ℝ) (c : ℝ) (h : ∀ s : S i, expectedPayoff u i (update x i (dirac s)) ≤ c)
    (y : S i → ℝ) (hy : y ∈ stdSimplex ℝ (S i)) :
    expectedPayoff u i (update x i y) ≤ c := by
  obtain ⟨hnn, hsum⟩ := hy
  rw [expectedPayoff_eq_sum_pure u i i (update x i y)]
  calc ∑ s : S i, (update x i y) i s * expectedPayoff u i (update (update x i y) i (dirac s))
      = ∑ s : S i, y s * expectedPayoff u i (update x i (dirac s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [update_idem, update_self]
    _ ≤ ∑ s : S i, y s * c := Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hnn s)
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

omit [∀ i, Nonempty (S i)] in
/-- The expected payoff at a pure profile is the payoff of that profile. -/
theorem expectedPayoff_pure (u : ι → (∀ i, S i) → ℝ) (i : ι) (p : ∀ i, S i) :
    expectedPayoff u i (fun j => dirac (p j)) = u i p := by
  rw [expectedPayoff, Finset.sum_eq_single p]
  · simp [dirac]
  · intro q _ hq
    have hj : ∃ j, q j ≠ p j := by
      by_contra hc
      push_neg at hc
      exact hq (funext hc)
    obtain ⟨j, hj⟩ := hj
    rw [Finset.prod_eq_zero (mem_univ j) (by simp [dirac, hj]), zero_mul]
  · simp

/-! ### Nash's map -/

/-- The (nonnegative) gain player `i` would get by switching to the pure strategy `s`. -/
noncomputable def gain (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : S i) (x : ∀ i, S i → ℝ) : ℝ :=
  max 0 (expectedPayoff u i (update x i (dirac s)) - expectedPayoff u i x)

/-- Nash's map: each player shifts weight towards the strategies that would improve their
payoff, and the result is renormalized. -/
noncomputable def nashMap (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i s => (x i s + gain u i s x) / (1 + ∑ t, gain u i t x)

omit [∀ i, Nonempty (S i)] in
theorem gain_nonneg (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : S i) (x : ∀ i, S i → ℝ) :
    0 ≤ gain u i s x := le_max_left _ _

omit [∀ i, Nonempty (S i)] in
theorem one_add_sum_gain_pos (u : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) :
    0 < 1 + ∑ t, gain u i t x := by
  have : 0 ≤ ∑ t, gain u i t x := Finset.sum_nonneg fun t _ => gain_nonneg u i t x
  linarith

omit [∀ i, Nonempty (S i)] in
theorem continuous_gain (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : S i) :
    Continuous (gain u i s) := by
  show Continuous fun x => max 0
    (expectedPayoff u i (update x i (dirac s)) - expectedPayoff u i x)
  exact continuous_const.max (((continuous_expectedPayoff u i).comp
    (Continuous.update continuous_id i continuous_const)).sub (continuous_expectedPayoff u i))

omit [∀ i, Nonempty (S i)] in
theorem continuous_nashMap (u : ι → (∀ i, S i) → ℝ) : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  have hden : Continuous fun x : (∀ i, S i → ℝ) => 1 + ∑ t, gain u i t x :=
    continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain u i t)
  exact (((continuous_apply s).comp (continuous_apply i)).add
    (continuous_gain u i s)).div hden fun x => (one_add_sum_gain_pos u i x).ne'

omit [∀ i, Nonempty (S i)] in
theorem nashMap_mapsTo (u : ι → (∀ i, S i) → ℝ) :
    Set.MapsTo (nashMap u) (strategyProfiles S) (strategyProfiles S) := by
  intro x hx i _
  obtain ⟨hnn, hsum⟩ := hx i (Set.mem_univ i)
  have hpos := one_add_sum_gain_pos u i x
  refine ⟨fun s => div_nonneg (add_nonneg (hnn s) (gain_nonneg u i s x)) hpos.le, ?_⟩
  simp only [nashMap]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hsum, div_self hpos.ne']

omit [∀ i, Nonempty (S i)] in
/-- At any mixed profile, some pure strategy in the support of player `i` does no better
than the profile itself. -/
theorem exists_support_not_better (u : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ)
    (hx : x ∈ strategyProfiles S) :
    ∃ s : S i, 0 < x i s ∧ expectedPayoff u i (update x i (dirac s)) ≤ expectedPayoff u i x := by
  by_contra hc
  push_neg at hc
  obtain ⟨hnn, hsum⟩ := hx i (Set.mem_univ i)
  have hex : ∃ s : S i, 0 < x i s := by
    by_contra h2
    push_neg at h2
    have hzero : ∑ s, x i s = 0 :=
      Finset.sum_eq_zero fun s _ => le_antisymm (h2 s) (hnn s)
    rw [hsum] at hzero
    exact one_ne_zero hzero
  obtain ⟨s1, hs1⟩ := hex
  have hlt : ∑ s : S i, x i s * expectedPayoff u i x
      < ∑ s : S i, x i s * expectedPayoff u i (update x i (dirac s)) := by
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s1, mem_univ s1, ?_⟩
    · rcases lt_or_eq_of_le (hnn s) with h | h
      · exact mul_le_mul_of_nonneg_left (hc s h).le h.le
      · rw [← h]; simp
    · exact mul_lt_mul_of_pos_left (hc s1 hs1) hs1
  rw [← Finset.sum_mul, hsum, one_mul, ← expectedPayoff_eq_sum_pure u i i x] at hlt
  exact lt_irrefl _ hlt

omit [∀ i, Nonempty (S i)] in
/-- A fixed point of Nash's map is a Nash equilibrium. -/
theorem isNashEquilibrium_of_fixed (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ)
    (hx : x ∈ strategyProfiles S) (hfix : nashMap u x = x) : IsNashEquilibrium u x := by
  refine ⟨hx, fun i y hy => ?_⟩
  have hpos := one_add_sum_gain_pos u i x
  have hcoord : ∀ s : S i, x i s * (∑ t, gain u i t x) = gain u i s x := by
    intro s
    have hs := congrFun (congrFun hfix i) s
    simp only [nashMap] at hs
    rw [div_eq_iff hpos.ne'] at hs
    nlinarith [hs]
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_not_better u i x hx
  have hg0 : gain u i s0 x = 0 := max_eq_left (by linarith)
  have hG0 : ∑ t, gain u i t x = 0 := by
    have h := hcoord s0
    rw [hg0] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hs0pos.ne'
    · exact h'
  have hall : ∀ t : S i, gain u i t x = 0 :=
    fun t => (Finset.sum_eq_zero_iff_of_nonneg fun t _ => gain_nonneg u i t x).mp hG0 t
      (mem_univ t)
  refine expectedPayoff_update_le_of_pure_le u i x _ (fun s => ?_) y hy
  have h := (le_max_right 0
    (expectedPayoff u i (update x i (dirac s)) - expectedPayoff u i x)).trans_eq (hall s)
  linarith

/-! ### The main theorem -/

/-- **Nash's theorem**: every finite game (finitely many players, each with a finite nonempty
set of pure strategies, and arbitrary real payoffs) has a mixed strategy Nash equilibrium.

This is the classical reduction of Nash's theorem to Brouwer's fixed point theorem, which is
taken here as an explicit hypothesis `hB` about the (finite dimensional) space of mixed
strategy profiles. -/
theorem nash_equilibrium_exists (hB : BrouwerFixedPointProperty (∀ i, S i → ℝ))
    (u : ι → (∀ i, S i) → ℝ) : ∃ x, IsNashEquilibrium u x := by
  obtain ⟨x, hxK, hfix⟩ := hB (strategyProfiles S) strategyProfiles_nonempty
    isCompact_strategyProfiles convex_strategyProfiles (nashMap u)
    (continuous_nashMap u).continuousOn (nashMap_mapsTo u)
  exact ⟨x, isNashEquilibrium_of_fixed u x hxK hfix⟩

/-! ### Unconditional special cases -/

omit [∀ i, Nonempty (S i)] in
/-- A pure profile no player can improve on by a unilateral pure deviation is a
(mixed) Nash equilibrium. -/
theorem isNashEquilibrium_pure (u : ι → (∀ i, S i) → ℝ) (p : ∀ i, S i)
    (hp : ∀ i (s : S i), u i (update p i s) ≤ u i p) :
    IsNashEquilibrium u (fun j => dirac (p j)) := by
  refine ⟨fun i _ => dirac_mem_stdSimplex (p i), fun i y hy => ?_⟩
  rw [expectedPayoff_pure]
  refine expectedPayoff_update_le_of_pure_le u i _ (u i p) (fun s => ?_) y hy
  have hupd : update (fun j => dirac (p j)) i (dirac s) = fun j => dirac ((update p i s) j) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj]
  rw [hupd, expectedPayoff_pure]
  exact hp i s

/-- `P` is an exact potential for the game `u`: any unilateral deviation changes the
deviating player's payoff exactly as much as it changes `P`. -/
def IsPotential (u : ι → (∀ i, S i) → ℝ) (P : (∀ i, S i) → ℝ) : Prop :=
  ∀ (i : ι) (p : ∀ i, S i) (s : S i), u i (update p i s) - u i p = P (update p i s) - P p

/-- Unconditionally (no fixed point theorem needed): every finite potential game — in
particular every game in which all players share a common payoff function — has a Nash
equilibrium, given by any profile maximizing the potential. -/
theorem nash_equilibrium_exists_of_potential (u : ι → (∀ i, S i) → ℝ) (P : (∀ i, S i) → ℝ)
    (h : IsPotential u P) : ∃ x, IsNashEquilibrium u x := by
  obtain ⟨p, hp⟩ := Finite.exists_max P
  refine ⟨fun j => dirac (p j), isNashEquilibrium_pure u p fun i s => ?_⟩
  have h1 := h i p s
  have h2 := hp (update p i s)
  linarith

end Game

end Frontier

import RequestProject.Nash

/-!
# Two-player finite games: the unconditional zero-sum case

This file proves, with no fixed point theorem, that every two-player finite **zero-sum**
game has a mixed strategy Nash equilibrium (a saddle point), together with the minimax
theorem.  The only non-elementary input is the separating hyperplane theorem.
-/

open Finset Set

namespace Frontier

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  [DecidableEq A] [DecidableEq B]

/-- The expected payoff `xᵀ M y` of the row player in a two-player game with payoff matrix
`M`, when the row player plays the mixed strategy `x` and the column player plays `y`. -/
noncomputable def bilin (M : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) : ℝ :=
  ∑ a, ∑ b, x a * y b * M a b

/-- `(x, y)` is a Nash equilibrium of the two-player game with payoff matrices `M` (row
player) and `N` (column player). -/
def IsTwoPlayerNash (M N : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) : Prop :=
  x ∈ stdSimplex ℝ A ∧ y ∈ stdSimplex ℝ B ∧
    (∀ x' ∈ stdSimplex ℝ A, bilin M x' y ≤ bilin M x y) ∧
    (∀ y' ∈ stdSimplex ℝ B, bilin N x y' ≤ bilin N x y)

/-- The value guaranteed to the row player by the mixed strategy `x`. -/
noncomputable def rowVal (M : A → B → ℝ) (x : A → ℝ) : ℝ :=
  univ.inf' univ_nonempty fun b => ∑ a, x a * M a b

/-- The most the column player can concede when playing the mixed strategy `y`. -/
noncomputable def colVal (M : A → B → ℝ) (y : B → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun a => ∑ b, y b * M a b

omit [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] in
theorem bilin_eq_sum_col (M : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) :
    bilin M x y = ∑ b, y b * ∑ a, x a * M a b := by
  rw [bilin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

omit [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] in
theorem bilin_eq_sum_row (M : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) :
    bilin M x y = ∑ a, x a * ∑ b, y b * M a b := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

omit [Nonempty A] [Nonempty B] [DecidableEq A] [DecidableEq B] in
theorem bilin_neg (M : A → B → ℝ) (x : A → ℝ) (y : B → ℝ) :
    bilin (fun a b => -M a b) x y = -bilin M x y := by
  simp only [bilin, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [Nonempty A] [DecidableEq A] [DecidableEq B] in
theorem rowVal_le_bilin (M : A → B → ℝ) {x : A → ℝ} {y : B → ℝ}
    (hy : y ∈ stdSimplex ℝ B) : rowVal M x ≤ bilin M x y := by
  obtain ⟨hnn, hsum⟩ := hy
  rw [bilin_eq_sum_col]
  calc rowVal M x = ∑ b, y b * rowVal M x := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ b, y b * ∑ a, x a * M a b :=
        Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left
            (Finset.inf'_le (fun b => ∑ a, x a * M a b) (Finset.mem_univ b)) (hnn b)

omit [Nonempty B] [DecidableEq A] [DecidableEq B] in
theorem bilin_le_colVal (M : A → B → ℝ) {x : A → ℝ} {y : B → ℝ}
    (hx : x ∈ stdSimplex ℝ A) : bilin M x y ≤ colVal M y := by
  obtain ⟨hnn, hsum⟩ := hx
  rw [bilin_eq_sum_row]
  calc ∑ a, x a * ∑ b, y b * M a b ≤ ∑ a, x a * colVal M y :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left
            (Finset.le_sup' (f := fun a => ∑ b, y b * M a b) (Finset.mem_univ a)) (hnn a)
    _ = colVal M y := by rw [← Finset.sum_mul, hsum, one_mul]

omit [Nonempty A] [DecidableEq A] [DecidableEq B] in
theorem continuous_rowVal (M : A → B → ℝ) : Continuous (rowVal M) :=
  Continuous.finset_inf'_apply univ_nonempty fun _ _ =>
    continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const

omit [Nonempty B] [DecidableEq A] [DecidableEq B] in
theorem continuous_colVal (M : A → B → ℝ) : Continuous (colVal M) :=
  Continuous.finset_sup'_apply univ_nonempty fun _ _ =>
    continuous_finset_sum _ fun b _ => (continuous_apply b).mul continuous_const

theorem stdSimplex_nonempty (A : Type*) [Fintype A] [Nonempty A] [DecidableEq A] :
    (stdSimplex ℝ A).Nonempty :=
  ⟨dirac (Classical.arbitrary A), dirac_mem_stdSimplex _⟩

omit [Nonempty A] in
/-- A theorem of the alternative, proved by separating a compact convex set from the
nonpositive orthant: either the row player has a mixed strategy that is strictly winning
against every column, or the column player has a mixed strategy that is at least as good
as a draw against every row. -/
theorem exists_pos_row_or_nonpos_col (M : A → B → ℝ) :
    (∃ x ∈ stdSimplex ℝ A, ∀ b, 0 < ∑ a, x a * M a b) ∨
      (∃ y ∈ stdSimplex ℝ B, ∀ a, ∑ b, y b * M a b ≤ 0) := by
  classical
  let L : (B → ℝ) →ₗ[ℝ] (A → ℝ) :=
    { toFun := fun y a => ∑ b, y b * M a b
      map_add' := by
        intro y z
        funext a
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        funext a
        simp [Finset.mul_sum, mul_assoc] }
  have hLapp : ∀ (y : B → ℝ) (a : A), L y a = ∑ b, y b * M a b := fun _ _ => rfl
  set K : Set (A → ℝ) := L '' (stdSimplex ℝ B)
  set T : Set (A → ℝ) := Set.pi Set.univ fun _ => Set.Iic (0 : ℝ)
  by_cases hmeet : (K ∩ T).Nonempty
  · right
    obtain ⟨v, ⟨y, hy, rfl⟩, hvT⟩ := hmeet
    exact ⟨y, hy, fun a => hvT a (Set.mem_univ a)⟩
  · left
    have hdisj : Disjoint K T :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)
    have hLcont : Continuous (fun y : B → ℝ => L y) :=
      continuous_pi fun a => continuous_finset_sum _ fun b _ =>
        (continuous_apply b).mul continuous_const
    have hKc : IsCompact K := (isCompact_stdSimplex B).image hLcont
    have hKconv : Convex ℝ K := (convex_stdSimplex ℝ B).linear_image L
    have hTc : IsClosed T := isClosed_set_pi fun _ _ => isClosed_Iic
    have hTconv : Convex ℝ T := convex_pi fun _ _ => convex_Iic 0
    obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
      geometric_hahn_banach_compact_closed hKconv hKc hTconv hTc hdisj
    -- coordinates of the separating functional
    set c : A → ℝ := fun a => f (Pi.single a 1)
    have hrep : ∀ w : A → ℝ, f w = ∑ a, w a * c a := by
      intro w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : (Pi.single a (w a) : A → ℝ) = w a • (Pi.single a (1 : ℝ) : A → ℝ) := by
        funext a'
        by_cases h : a' = a <;> simp [Pi.single_apply, h]
      rw [h1, map_smul, smul_eq_mul]
    have h0T : (0 : A → ℝ) ∈ T := fun a _ => Set.mem_Iic.mpr le_rfl
    have hv0 : v < 0 := by simpa using hfT 0 h0T
    have hu0 : u < 0 := lt_trans huv hv0
    -- the coordinates are nonpositive
    have hcnonpos : ∀ a, c a ≤ 0 := by
      intro a
      by_contra hpos
      push_neg at hpos
      obtain ⟨n, hn⟩ := exists_nat_gt (-v / c a)
      set t : A → ℝ := fun a' => if a' = a then -(n : ℝ) else 0 with htdef
      have htT : t ∈ T := by
        intro a' _
        simp only [htdef, Set.mem_Iic]
        split
        · simp
        · exact le_rfl
      have hft := hfT t htT
      rw [hrep t] at hft
      have hsum : ∑ a', t a' * c a' = -(n : ℝ) * c a := by
        rw [Finset.sum_eq_single a]
        · simp [htdef]
        · intro a' _ hne
          simp [htdef, hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
      rw [hsum] at hft
      have : -v < (n : ℝ) * c a := by
        rw [div_lt_iff₀ hpos] at hn
        linarith
      linarith
    -- the separating functional is not zero
    obtain ⟨y0, hy0⟩ := stdSimplex_nonempty B
    have hKne : L y0 ∈ K := ⟨y0, hy0, rfl⟩
    have hfneg : f (L y0) < 0 := lt_trans (hfK _ hKne) hu0
    have hex : ∃ a, c a ≠ 0 := by
      by_contra hall
      push_neg at hall
      rw [hrep (L y0)] at hfneg
      simp [hall] at hfneg
    obtain ⟨a0, ha0⟩ := hex
    have hs : ∑ a, c a < 0 := by
      have := Finset.sum_lt_sum (f := c) (g := fun _ : A => (0 : ℝ))
        (fun a _ => hcnonpos a) ⟨a0, mem_univ a0, lt_of_le_of_ne (hcnonpos a0) ha0⟩
      simpa using this
    refine ⟨fun a => c a / ∑ a', c a', ⟨fun a => ?_, ?_⟩, fun b => ?_⟩
    · rw [div_nonneg_iff]
      exact Or.inr ⟨hcnonpos a, hs.le⟩
    · rw [← Finset.sum_div, div_self hs.ne]
    · have hmem : (fun a => M a b) ∈ K := by
        refine ⟨dirac b, dirac_mem_stdSimplex b, ?_⟩
        funext a
        rw [hLapp]
        simp [dirac]
      have hlt : f (fun a => M a b) < 0 := lt_trans (hfK _ hmem) hu0
      rw [hrep] at hlt
      have hrw : ∑ a, c a / (∑ a', c a') * M a b = (∑ a, M a b * c a) / (∑ a', c a') := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hrw]
      exact div_pos_of_neg_of_neg hlt hs

/-- **The minimax theorem** for finite two-player zero-sum games: the row player has a mixed
strategy guaranteeing a value that the column player can simultaneously hold them to. -/
theorem minimax (M : A → B → ℝ) :
    ∃ x ∈ stdSimplex ℝ A, ∃ y ∈ stdSimplex ℝ B, rowVal M x = colVal M y := by
  obtain ⟨x0, hx0, hx0max⟩ := (isCompact_stdSimplex A).exists_isMaxOn
    (stdSimplex_nonempty A) (continuous_rowVal M).continuousOn
  obtain ⟨y0, hy0, hy0min⟩ := (isCompact_stdSimplex B).exists_isMinOn
    (stdSimplex_nonempty B) (continuous_colVal M).continuousOn
  refine ⟨x0, hx0, y0, hy0, le_antisymm ((rowVal_le_bilin M hy0).trans (bilin_le_colVal M hx0)) ?_⟩
  by_contra hlt
  push_neg at hlt
  set c : ℝ := (rowVal M x0 + colVal M y0) / 2 with hcdef
  have hc1 : rowVal M x0 < c := by simp only [hcdef]; linarith
  have hc2 : c < colVal M y0 := by simp only [hcdef]; linarith
  rcases exists_pos_row_or_nonpos_col (fun a b => M a b - c) with ⟨x, hx, hxpos⟩ | ⟨y, hy, hyle⟩
  · have hxsum := hx.2
    have hcle : c ≤ rowVal M x := by
      refine Finset.le_inf' _ _ fun b _ => ?_
      have := hxpos b
      have hexp : ∑ a, x a * (M a b - c) = (∑ a, x a * M a b) - c := by
        rw [show ∑ a, x a * (M a b - c) = (∑ a, x a * M a b) - (∑ a, x a) * c by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring, hxsum, one_mul]
      rw [hexp] at this
      linarith
    have := hx0max hx
    simp only [Set.mem_setOf_eq] at this
    linarith
  · have hysum := hy.2
    have hcge : colVal M y ≤ c := by
      refine Finset.sup'_le _ _ fun a _ => ?_
      have := hyle a
      have hexp : ∑ b, y b * (M a b - c) = (∑ b, y b * M a b) - c := by
        rw [show ∑ b, y b * (M a b - c) = (∑ b, y b * M a b) - (∑ b, y b) * c by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun b _ => by ring, hysum, one_mul]
      rw [hexp] at this
      linarith
    have := hy0min hy
    simp only [Set.mem_setOf_eq] at this
    linarith

/-- **Existence of a saddle point** for every finite two-player zero-sum game. -/
theorem exists_saddlePoint (M : A → B → ℝ) :
    ∃ x ∈ stdSimplex ℝ A, ∃ y ∈ stdSimplex ℝ B,
      (∀ x' ∈ stdSimplex ℝ A, bilin M x' y ≤ bilin M x y) ∧
        (∀ y' ∈ stdSimplex ℝ B, bilin M x y ≤ bilin M x y') := by
  obtain ⟨x, hx, y, hy, hval⟩ := minimax M
  refine ⟨x, hx, y, hy, fun x' hx' => ?_, fun y' hy' => ?_⟩
  · exact ((bilin_le_colVal M hx').trans_eq hval.symm).trans (rowVal_le_bilin M hy)
  · exact ((bilin_le_colVal M hx).trans_eq hval.symm).trans (rowVal_le_bilin M hy')

/-- Unconditionally (no fixed point theorem needed): every finite two-player zero-sum game
has a mixed strategy Nash equilibrium. -/
theorem zerosum_nash_equilibrium_exists (M : A → B → ℝ) :
    ∃ x y, IsTwoPlayerNash M (fun a b => -M a b) x y := by
  obtain ⟨x, hx, y, hy, h1, h2⟩ := exists_saddlePoint M
  refine ⟨x, y, hx, hy, h1, fun y' hy' => ?_⟩
  rw [bilin_neg, bilin_neg, neg_le_neg_iff]
  exact h2 y' hy'

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

