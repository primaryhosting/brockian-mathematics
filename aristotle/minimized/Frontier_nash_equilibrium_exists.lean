import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires `import` to be the very first command in a file, so the header comment
above is placed immediately after it.)
-/

open scoped BigOperators

namespace Frontier

section Defs

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `a`, viewed as a (degenerate) mixed strategy. -/

def pureStrat {i : ι} (a : S i) : S i → ℝ := fun b => if b = a then 1 else 0

/-- The set of mixed strategy profiles: each player `i` picks a probability
distribution on their finite pure strategy set `S i`. -/

def MixedProfiles (S : ι → Type) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  {x | ∀ i, x i ∈ stdSimplex ℝ (S i)}

/-- The expected payoff of player `i` under the mixed profile `x`, for the game with
pure payoff functions `g`. -/

def expectedPayoff (g : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) : ℝ :=
  ∑ s : (∀ i, S i), (∏ j, x j (s j)) * g i s

/-- The expected payoff to player `i` when they deviate to the pure strategy `a`. -/

def deviationPayoff (g : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) (a : S i) : ℝ :=
  expectedPayoff g i (Function.update x i (pureStrat a))

/-- `x` is a mixed-strategy Nash equilibrium of the finite game with payoffs `g`:
it is a mixed profile, and no player can strictly improve their expected payoff by
unilaterally switching to another mixed strategy. -/

def IsNashEquilibrium (g : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : Prop :=
  x ∈ MixedProfiles S ∧
    ∀ i, ∀ y ∈ stdSimplex ℝ (S i),
      expectedPayoff g i (Function.update x i y) ≤ expectedPayoff g i x

/-- `s` is a pure-strategy Nash equilibrium: no player can improve by switching to
another pure strategy. -/

def BrouwerFixedPointProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
      ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

section Basic

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  {g : ι → (∀ i, S i) → ℝ}

theorem pureStrat_mem_stdSimplex {i : ι} (a : S i) : pureStrat a ∈ stdSimplex ℝ (S i) := by
  constructor
  · intro b
    by_cases h : b = a <;> simp [pureStrat, h]
  · simp [pureStrat]

theorem prod_update (i : ι) (x : ∀ i, S i → ℝ) (y : S i → ℝ) (s : ∀ j, S j) :
    (∏ j, Function.update x i y j (s j))
      = y (s i) * ∏ j ∈ Finset.univ.erase i, x j (s j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The expected payoff is multilinear: as a function of player `i`'s mixed strategy it is
linear, so it is the corresponding convex combination of the pure deviation payoffs. -/

theorem expectedPayoff_update (i : ι) (x : ∀ i, S i → ℝ) (y : S i → ℝ) :
    expectedPayoff g i (Function.update x i y) = ∑ a : S i, y a * deviationPayoff g i x a := by
  have hL : expectedPayoff g i (Function.update x i y)
      = ∑ s : (∀ j, S j), y (s i) * ((∏ j ∈ Finset.univ.erase i, x j (s j)) * g i s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_update i x y s, mul_assoc]
  have hR : ∀ a : S i, deviationPayoff g i x a
      = ∑ s : (∀ j, S j),
          (if s i = a then (1 : ℝ) else 0) * ((∏ j ∈ Finset.univ.erase i, x j (s j)) * g i s) := by
    intro a
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_update i x (pureStrat a) s, mul_assoc]
    rfl
  rw [hL]
  simp_rw [hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

theorem expectedPayoff_eq_sum (i : ι) (x : ∀ i, S i → ℝ) :
    expectedPayoff g i x = ∑ a : S i, x i a * deviationPayoff g i x a := by
  conv_lhs => rw [← Function.update_eq_self i x]
  rw [expectedPayoff_update]

/-- A mixed profile is a Nash equilibrium iff no *pure* deviation is profitable. -/

theorem isNashEquilibrium_iff {x : ∀ i, S i → ℝ} (hx : x ∈ MixedProfiles S) :
    IsNashEquilibrium g x ↔ ∀ (i : ι) (a : S i), deviationPayoff g i x a ≤ expectedPayoff g i x := by
  constructor
  · rintro ⟨-, h⟩ i a
    exact h i (pureStrat a) (pureStrat_mem_stdSimplex a)
  · intro h
    refine ⟨hx, fun i y hy => ?_⟩
    rw [expectedPayoff_update]
    calc ∑ a : S i, y a * deviationPayoff g i x a
        ≤ ∑ a : S i, y a * expectedPayoff g i x := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (h i a) (hy.1 a)
      _ = expectedPayoff g i x := by rw [← Finset.sum_mul, hy.2, one_mul]

theorem continuous_expectedPayoff (i : ι) :
    Continuous fun x : (∀ i, S i → ℝ) => expectedPayoff g i x := by
  refine continuous_finset_sum _ fun s _ => ?_
  exact ((continuous_finset_prod _ fun j _ => (continuous_apply (s j)).comp
    (continuous_apply (A := fun j => S j → ℝ) j)).mul continuous_const)

theorem continuous_update (i : ι) (y : S i → ℝ) :
    Continuous fun x : (∀ j, S j → ℝ) => Function.update x i y := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa [Function.update_self] using (continuous_const : Continuous fun _ : (∀ j, S j → ℝ) => y)
  · simpa [Function.update_of_ne h] using
      (continuous_apply (A := fun j => S j → ℝ) j)

theorem continuous_deviationPayoff (i : ι) (a : S i) :
    Continuous fun x : (∀ i, S i → ℝ) => deviationPayoff g i x a :=
  (continuous_expectedPayoff i).comp (continuous_update i (pureStrat a))

theorem mixedProfiles_eq_pi :
    MixedProfiles S = Set.univ.pi fun i => stdSimplex ℝ (S i) := by
  ext x
  simp [MixedProfiles]

theorem isCompact_mixedProfiles : IsCompact (MixedProfiles S) := by
  rw [mixedProfiles_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_stdSimplex _

theorem convex_mixedProfiles : Convex ℝ (MixedProfiles S) := by
  rw [mixedProfiles_eq_pi]
  exact convex_pi fun i _ => convex_stdSimplex ℝ (S i)

theorem nonempty_mixedProfiles [∀ i, Nonempty (S i)] : (MixedProfiles S).Nonempty :=
  ⟨fun i => pureStrat (Classical.arbitrary (S i)), fun i => pureStrat_mem_stdSimplex _⟩

end Basic

section NashMap

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The regret of player `i` at `x` for the pure strategy `a`: the (nonnegative part of the)
gain from deviating to `a`. -/

def gain (g : ι → (∀ i, S i) → ℝ) (i : ι) (x : ∀ i, S i → ℝ) (a : S i) : ℝ :=
  max 0 (deviationPayoff g i x a - expectedPayoff g i x)

/-- Nash's map: shift each player's mixed strategy towards its profitable deviations and
renormalize. -/

noncomputable def nashMap (g : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) : ∀ i, S i → ℝ :=
  fun i a => (x i a + gain g i x a) / (1 + ∑ b : S i, gain g i x b)

variable {g : ι → (∀ i, S i) → ℝ}

theorem gain_nonneg (i : ι) (x : ∀ i, S i → ℝ) (a : S i) : 0 ≤ gain g i x a :=
  le_max_left _ _

theorem sum_gain_nonneg (i : ι) (x : ∀ i, S i → ℝ) : 0 ≤ ∑ b : S i, gain g i x b :=
  Finset.sum_nonneg fun b _ => gain_nonneg i x b

theorem gain_denom_pos (i : ι) (x : ∀ i, S i → ℝ) :
    (0 : ℝ) < 1 + ∑ b : S i, gain g i x b := by
  have := sum_gain_nonneg i x (g := g)
  linarith

theorem continuous_gain (i : ι) (a : S i) :
    Continuous fun x : (∀ i, S i → ℝ) => gain g i x a :=
  continuous_const.max ((continuous_deviationPayoff i a).sub (continuous_expectedPayoff i))

theorem continuous_nashMap : Continuous (nashMap g) := by
  refine continuous_pi fun i => continuous_pi fun a => ?_
  refine Continuous.div
    (((continuous_apply a).comp (continuous_apply (A := fun j => S j → ℝ) i)).add
      (continuous_gain i a))
    (continuous_const.add (continuous_finset_sum _ fun b _ => continuous_gain i b))
    (fun x => ne_of_gt (gain_denom_pos i x))

theorem nashMap_mapsTo : Set.MapsTo (nashMap g) (MixedProfiles S) (MixedProfiles S) := by
  intro x hx i
  have hden : (0 : ℝ) < 1 + ∑ b : S i, gain g i x b := gain_denom_pos i x
  constructor
  · intro a
    exact div_nonneg (add_nonneg ((hx i).1 a) (gain_nonneg i x a)) hden.le
  · simp only [nashMap]
    rw [← Finset.sum_div, Finset.sum_add_distrib, (hx i).2]
    exact div_self (ne_of_gt hden)

/-- A fixed point of Nash's map inside the mixed profiles is a Nash equilibrium. -/

theorem isNashEquilibrium_of_fixed {x : ∀ i, S i → ℝ} (hx : x ∈ MixedProfiles S)
    (hfix : nashMap g x = x) : IsNashEquilibrium g x := by
  rw [isNashEquilibrium_iff hx]
  intro i
  have hden : (0 : ℝ) < 1 + ∑ b : S i, gain g i x b := gain_denom_pos i x
  -- at a fixed point, each regret is proportional to the probability weight
  have key : ∀ a : S i, gain g i x a = x i a * ∑ b : S i, gain g i x b := by
    intro a
    have h := congrFun (congrFun hfix i) a
    simp only [nashMap] at h
    rw [div_eq_iff (ne_of_gt hden)] at h
    linear_combination h
  have hnn : ∀ a : S i, 0 ≤ x i a := (hx i).1
  have hsum1 : ∑ a : S i, x i a = 1 := (hx i).2
  -- some strategy in the support does no better than average
  have hstep : ∃ a : S i, x i a ≠ 0 ∧ deviationPayoff g i x a ≤ expectedPayoff g i x := by
    by_contra hcon
    push_neg at hcon
    have hv : expectedPayoff g i x = ∑ a : S i, x i a * deviationPayoff g i x a :=
      expectedPayoff_eq_sum i x
    obtain ⟨a₀, ha₀⟩ : ∃ a : S i, x i a ≠ 0 := by
      by_contra h
      push_neg at h
      rw [Finset.sum_congr rfl fun a _ => h a] at hsum1
      simp at hsum1
    have hlt : ∑ a : S i, x i a * expectedPayoff g i x
        < ∑ a : S i, x i a * deviationPayoff g i x a := by
      refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
      · rcases eq_or_lt_of_le (hnn a) with h | h
        · simp [← h]
        · exact mul_le_mul_of_nonneg_left (hcon a (ne_of_gt h)).le h.le
      · exact mul_lt_mul_of_pos_left (hcon a₀ ha₀) (lt_of_le_of_ne (hnn a₀) (Ne.symm ha₀))
    rw [← Finset.sum_mul, hsum1, one_mul] at hlt
    exact absurd hv (ne_of_lt hlt)
  obtain ⟨a₀, hne, hle⟩ := hstep
  have hg0 : gain g i x a₀ = 0 := max_eq_left (by linarith)
  have hDzero : ∑ b : S i, gain g i x b = 0 := by
    have := key a₀
    rw [hg0] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hne
    · exact h
  intro a
  have h0 : gain g i x a = 0 := by rw [key a, hDzero, mul_zero]
  have hmax : deviationPayoff g i x a - expectedPayoff g i x ≤ gain g i x a := le_max_right _ _
  linarith

end NashMap

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]

/-- **Nash's theorem**: every finite game (finitely many players, each with a finite nonempty
set of pure strategies, and arbitrary real payoffs) has a mixed-strategy Nash equilibrium.

This is a Lean-checked reduction to Brouwer's fixed point theorem (hypothesis `hB`), which is
not available in Mathlib; everything else — Nash's map, its continuity, that it preserves the
product of simplices, and that its fixed points are exactly the equilibria — is proved here. -/

theorem nash_equilibrium_exists (hB : BrouwerFixedPointProperty) (g : ι → (∀ i, S i) → ℝ) :
    ∃ x, IsNashEquilibrium g x := by
  obtain ⟨x, hxK, hfix⟩ :=
    hB (∀ i, S i → ℝ) (MixedProfiles S) nonempty_mixedProfiles isCompact_mixedProfiles
      convex_mixedProfiles (nashMap g) continuous_nashMap.continuousOn nashMap_mapsTo
  exact ⟨x, isNashEquilibrium_of_fixed hxK hfix⟩

end Main

section Unconditional

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
  {g : ι → (∀ i, S i) → ℝ}

/-- The Dirac mixed profile concentrated on the pure profile `s`. -/
