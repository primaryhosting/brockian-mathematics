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

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/
def IsDist {i : ι} (z : S i → ℝ) : Prop := (∀ s, 0 ≤ z s) ∧ ∑ s, z s = 1

/-- A mixed strategy profile: each player plays a distribution over their pure strategies. -/
def IsMixed (x : ∀ i, S i → ℝ) : Prop := ∀ i, IsDist (x i)

/-- The set of mixed strategy profiles. -/
def mixedProfiles (S : ι → Type) [∀ i, Fintype (S i)] : Set (∀ i, S i → ℝ) :=
  {x | IsMixed x}

/-- Expected payoff of player `i` under the mixed profile `x`, for the payoff
functions `u`. -/
noncomputable def payoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) : ℝ :=
  ∑ p : (∀ j, S j), (∏ j, x j (p j)) * u i p

/-- `x` is a (mixed strategy) Nash equilibrium: it is a mixed profile, and no player can
strictly increase their expected payoff by unilaterally switching to another mixed strategy. -/
def IsNashEquilibrium (u : ι → (∀ j, S j) → ℝ) (x : ∀ j, S j → ℝ) : Prop :=
  IsMixed x ∧ ∀ (i : ι) (z : S i → ℝ), IsDist z →
    payoff u i (Function.update x i z) ≤ payoff u i x

/-- Brouwer's fixed point theorem for the space `E`: every continuous self-map of a
nonempty compact convex subset of `E` has a fixed point. (This is not available in
Mathlib, so it is taken as an explicit hypothesis.) -/
def BrouwerFixedPoint (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ K : Set E, K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, ContinuousOn f K → Set.MapsTo f K K → ∃ x ∈ K, f x = x

/-! ## Payoff algebra -/

/-- Expected payoff of player `i` when they play the pure strategy `s` and the others
play according to `x` (the `i`-th coordinate of `x` is ignored). -/
noncomputable def devPayoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i)
    (x : ∀ j, S j → ℝ) : ℝ :=
  ∑ p : (∀ j, S j), (if p i = s then (1 : ℝ) else 0) *
    ((∏ j ∈ univ.erase i, x j (p j)) * u i p)

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
lemma prod_update_eq {i : ι} (x : ∀ j, S j → ℝ) (z : S i → ℝ) (p : ∀ j, S j) :
    (∏ j, (Function.update x i z) j (p j))
      = z (p i) * ∏ j ∈ univ.erase i, x j (p j) := by
  rw [← Finset.mul_prod_erase univ (fun j => (Function.update x i z) j (p j)) (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [∀ i, DecidableEq (S i)] in
lemma payoff_update (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) (z : S i → ℝ) :
    payoff u i (Function.update x i z)
      = ∑ p : (∀ j, S j), z (p i) * ((∏ j ∈ univ.erase i, x j (p j)) * u i p) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [prod_update_eq, mul_assoc]

/-- The expected payoff is linear in the deviating player's mixed strategy. -/
lemma payoff_update_eq_sum (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ)
    (z : S i → ℝ) :
    payoff u i (Function.update x i z) = ∑ s, z s * devPayoff u i s x := by
  rw [payoff_update]
  simp only [devPayoff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (p i)]
  · simp
  · intro s _ hs
    simp [Ne.symm hs]
  · intro h
    exact absurd (mem_univ (p i)) h

lemma payoff_eq_sum (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) :
    payoff u i x = ∑ s, x i s * devPayoff u i s x := by
  conv_lhs => rw [← Function.update_eq_self i x]
  exact payoff_update_eq_sum u i x (x i)

/-- A profile all of whose pure deviations are unprofitable is a Nash equilibrium. -/
lemma isNashEquilibrium_of_pure (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ}
    (hx : IsMixed x) (h : ∀ (i : ι) (s : S i), devPayoff u i s x ≤ payoff u i x) :
    IsNashEquilibrium u x := by
  refine ⟨hx, fun i z hz => ?_⟩
  rw [payoff_update_eq_sum]
  calc ∑ s, z s * devPayoff u i s x ≤ ∑ _s : S i, z _s * payoff u i x := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (h i s) (hz.1 s)
    _ = payoff u i x := by rw [← Finset.sum_mul, hz.2, one_mul]

/-! ## The strategy space is nonempty, compact and convex -/

omit [Fintype ι] [DecidableEq ι] in
lemma mixedProfiles_nonempty [∀ i, Nonempty (S i)] :
    (mixedProfiles S).Nonempty := by
  refine ⟨fun i s => if s = Classical.arbitrary (S i) then 1 else 0, fun i => ⟨fun s => ?_, ?_⟩⟩
  · dsimp only
    split <;> norm_num
  · simp

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
lemma mixedProfiles_convex : Convex ℝ (mixedProfiles S) := by
  intro x hx y hy a b ha hb hab i
  refine ⟨fun s => ?_, ?_⟩
  · have := (hx i).1 s
    have := (hy i).1 s
    have h1 : 0 ≤ a * x i s := mul_nonneg ha ((hx i).1 s)
    have h2 : 0 ≤ b * y i s := mul_nonneg hb ((hy i).1 s)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hx i).2, (hy i).2,
      mul_one, mul_one, hab]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
lemma continuous_coord (i : ι) (s : S i) :
    Continuous (fun x : (∀ j, S j → ℝ) => x i s) :=
  (continuous_apply s).comp (continuous_apply i)

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
lemma mixedProfiles_isClosed : IsClosed (mixedProfiles S) := by
  have h1 : mixedProfiles S =
      (⋂ i : ι, ⋂ s : S i, {x : ∀ j, S j → ℝ | 0 ≤ x i s}) ∩
        (⋂ i : ι, {x : ∀ j, S j → ℝ | ∑ s, x i s = 1}) := by
    ext x
    simp only [mixedProfiles, IsMixed, IsDist, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    constructor
    · exact fun h => ⟨fun i s => (h i).1 s, fun i => (h i).2⟩
    · exact fun h i => ⟨fun s => h.1 i s, h.2 i⟩
  rw [h1]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun s =>
      isClosed_le continuous_const (continuous_coord i s)
  · exact isClosed_iInter fun i =>
      isClosed_eq (continuous_finset_sum _ fun s _ => continuous_coord i s) continuous_const

omit [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (S i)] in
lemma mixedProfiles_isCompact : IsCompact (mixedProfiles S) := by
  have hbox : IsCompact (Set.pi Set.univ
      (fun i : ι => Set.pi Set.univ (fun _ : S i => Set.Icc (0 : ℝ) 1))) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset mixedProfiles_isClosed ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  intro i s
  refine ⟨(hx i).1 s, ?_⟩
  have : x i s ≤ ∑ t, x i t :=
    Finset.single_le_sum (f := fun t => x i t) (fun t _ => (hx i).1 t) (mem_univ s)
  rw [(hx i).2] at this
  exact this

/-! ## Nash's map -/

/-- The gain of player `i` from switching to the pure strategy `s`, truncated at `0`. -/
noncomputable def gain (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) (x : ∀ j, S j → ℝ) : ℝ :=
  max 0 (devPayoff u i s x - payoff u i x)

/-- Nash's map: reweight each player's strategy by its gain, then renormalize. -/
noncomputable def nashMap (u : ι → (∀ j, S j) → ℝ) (x : ∀ j, S j → ℝ) : ∀ j, S j → ℝ :=
  fun i s => (x i s + gain u i s x) / (1 + ∑ t, gain u i t x)

lemma gain_nonneg (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) (x : ∀ j, S j → ℝ) :
    0 ≤ gain u i s x := le_max_left _ _

lemma one_le_denom (u : ι → (∀ j, S j) → ℝ) (i : ι) (x : ∀ j, S j → ℝ) :
    (1 : ℝ) ≤ 1 + ∑ t, gain u i t x := by
  have : (0 : ℝ) ≤ ∑ t, gain u i t x :=
    Finset.sum_nonneg fun t _ => gain_nonneg u i t x
  linarith

omit [∀ i, DecidableEq (S i)] in
lemma continuous_payoff (u : ι → (∀ j, S j) → ℝ) (i : ι) :
    Continuous (payoff u i) := by
  refine continuous_finset_sum _ fun p _ => ?_
  exact (continuous_finset_prod _ fun j _ => continuous_coord j (p j)).mul continuous_const

lemma continuous_devPayoff (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) :
    Continuous (devPayoff u i s) := by
  refine continuous_finset_sum _ fun p _ => ?_
  exact continuous_const.mul
    ((continuous_finset_prod _ fun j _ => continuous_coord j (p j)).mul continuous_const)

lemma continuous_gain (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) :
    Continuous (gain u i s) :=
  continuous_const.max ((continuous_devPayoff u i s).sub (continuous_payoff u i))

lemma continuous_nashMap (u : ι → (∀ j, S j) → ℝ) : Continuous (nashMap u) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  refine Continuous.div ((continuous_coord i s).add (continuous_gain u i s))
    (continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain u i t)) ?_
  intro x
  have := one_le_denom u i x
  linarith

lemma nashMap_mapsTo (u : ι → (∀ j, S j) → ℝ) :
    Set.MapsTo (nashMap u) (mixedProfiles S) (mixedProfiles S) := by
  intro x hx i
  have hden : (0 : ℝ) < 1 + ∑ t, gain u i t x := lt_of_lt_of_le zero_lt_one (one_le_denom u i x)
  refine ⟨fun s => ?_, ?_⟩
  · exact div_nonneg (add_nonneg ((hx i).1 s) (gain_nonneg u i s x)) hden.le
  · show ∑ s, (x i s + gain u i s x) / (1 + ∑ t, gain u i t x) = 1
    rw [← Finset.sum_div, Finset.sum_add_distrib, (hx i).2, div_self hden.ne']

/-- In any mixed profile some strategy in the support of player `i` is not better than
the profile itself. -/
lemma exists_support_le (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ} (hx : IsMixed x)
    (i : ι) : ∃ s : S i, 0 < x i s ∧ devPayoff u i s x ≤ payoff u i x := by
  classical
  set T : Finset (S i) := univ.filter (fun s => 0 < x i s) with hT
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ s : S i, x i s = 0 := by
      intro s
      rcases lt_or_eq_of_le ((hx i).1 s) with hlt | heq
      · exact absurd (Finset.mem_filter.mpr ⟨mem_univ s, hlt⟩) (by rw [← hT, h]; simp)
      · exact heq.symm
    have := (hx i).2
    rw [Finset.sum_congr rfl fun s _ => hzero s] at this
    simp at this
  obtain ⟨s0, hs0T, hs0min⟩ := T.exists_min_image (fun s => devPayoff u i s x) hTne
  have hs0pos : 0 < x i s0 := (Finset.mem_filter.mp hs0T).2
  refine ⟨s0, hs0pos, ?_⟩
  have hle : ∑ s, x i s * devPayoff u i s0 x ≤ ∑ s, x i s * devPayoff u i s x := by
    refine Finset.sum_le_sum fun s _ => ?_
    rcases lt_or_eq_of_le ((hx i).1 s) with hlt | heq
    · exact mul_le_mul_of_nonneg_left
        (hs0min s (Finset.mem_filter.mpr ⟨mem_univ s, hlt⟩)) hlt.le
    · rw [← heq]; simp
  rw [← Finset.sum_mul, (hx i).2, one_mul] at hle
  rw [payoff_eq_sum]
  exact hle

/-- A fixed point of Nash's map is a Nash equilibrium. -/
lemma isNashEquilibrium_of_fixed (u : ι → (∀ j, S j) → ℝ) {x : ∀ j, S j → ℝ}
    (hx : IsMixed x) (hfix : nashMap u x = x) : IsNashEquilibrium u x := by
  refine isNashEquilibrium_of_pure u hx fun i s => ?_
  have hden : (0 : ℝ) < 1 + ∑ t, gain u i t x := lt_of_lt_of_le zero_lt_one (one_le_denom u i x)
  have key : ∀ t : S i, x i t * (∑ r, gain u i r x) = gain u i t x := by
    intro t
    have h := congrFun (congrFun hfix i) t
    have h' : (x i t + gain u i t x) / (1 + ∑ r, gain u i r x) = x i t := h
    field_simp at h'
    linarith [h']
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_le u hx i
  have hg0 : gain u i s0 x = 0 := by
    simp only [gain]
    exact max_eq_left (by linarith)
  have hG : (∑ r, gain u i r x) = 0 := by
    have := key s0
    rw [hg0] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hs0pos.ne'
    · exact h
  have hgs : gain u i s x = 0 := by rw [← key s, hG, mul_zero]
  have : devPayoff u i s x - payoff u i x ≤ 0 := by
    have : max 0 (devPayoff u i s x - payoff u i x) = 0 := hgs
    exact max_eq_left_iff.mp this
  linarith

/-! ## Nash's theorem -/

/-- **Nash's theorem** (reduction to Brouwer's fixed point theorem): every finite game in
normal form, given by a finite set of players `ι`, finite nonempty pure strategy sets
`S i` and payoff functions `u i`, has a mixed strategy Nash equilibrium. -/
theorem nash_equilibrium_exists [∀ i, Nonempty (S i)]
    (hB : BrouwerFixedPoint (∀ i, S i → ℝ)) (u : ι → (∀ j, S j) → ℝ) :
    ∃ x : ∀ j, S j → ℝ, IsNashEquilibrium u x := by
  obtain ⟨x, hxK, hfix⟩ := hB (mixedProfiles S) mixedProfiles_nonempty
    mixedProfiles_isCompact mixedProfiles_convex (nashMap u)
    (continuous_nashMap u).continuousOn (nashMap_mapsTo u)
  exact ⟨x, isNashEquilibrium_of_fixed u hxK hfix⟩

/-! ## Unconditional existence for potential games

The reduction above needs Brouwer's fixed point theorem. For the special case of
*potential games* (which includes games of common interest) a pure strategy equilibrium
exists unconditionally: any maximizer of the potential is one. -/

/-- The mixed profile in which every player `j` plays the pure strategy `p j`. -/
def pureProfile (p : ∀ j, S j) : ∀ j, S j → ℝ := fun j t => if t = p j then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
lemma isMixed_pureProfile (p : ∀ j, S j) : IsMixed (pureProfile p) := by
  intro i
  refine ⟨fun s => ?_, ?_⟩
  · dsimp only [pureProfile]
    split <;> norm_num
  · simp [pureProfile]

lemma devPayoff_pureProfile (u : ι → (∀ j, S j) → ℝ) (i : ι) (s : S i) (p : ∀ j, S j) :
    devPayoff u i s (pureProfile p) = u i (Function.update p i s) := by
  classical
  rw [devPayoff, Finset.sum_eq_single (Function.update p i s)]
  · have h1 : (Function.update p i s) i = s := Function.update_self ..
    rw [h1]
    have h2 : ∀ j ∈ univ.erase i,
        pureProfile p j ((Function.update p i s) j) = 1 := by
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp [pureProfile]
    rw [Finset.prod_congr rfl h2]
    simp
  · intro q _ hq
    by_cases hqi : q i = s
    · have : ∃ j ∈ univ.erase i, q j ≠ p j := by
        by_contra hcon
        push_neg at hcon
        exact hq (funext fun j => by
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]; exact hqi
          · rw [Function.update_of_ne hji]
            exact hcon j (Finset.mem_erase.mpr ⟨hji, mem_univ j⟩))
      obtain ⟨j, hj, hjne⟩ := this
      have : (∏ k ∈ univ.erase i, pureProfile p k (q k)) = 0 :=
        Finset.prod_eq_zero hj (by simp [pureProfile, hjne])
      rw [this]
      ring
    · simp [hqi]
  · intro h
    exact absurd (mem_univ (Function.update p i s)) h

lemma payoff_pureProfile (u : ι → (∀ j, S j) → ℝ) (i : ι) (p : ∀ j, S j) :
    payoff u i (pureProfile p) = u i p := by
  classical
  rw [payoff_eq_sum, Finset.sum_eq_single (p i)]
  · rw [devPayoff_pureProfile, Function.update_eq_self]
    simp [pureProfile]
  · intro s _ hs
    simp [pureProfile, hs]
  · intro h
    exact absurd (mem_univ (p i)) h

/-- **Unconditional existence in potential games.** If the game admits an exact potential
`P`, i.e. every unilateral deviation changes the deviating player's payoff by exactly the
change in `P`, then a maximizer of `P` yields a (pure) Nash equilibrium. No fixed point
theorem is needed. -/
theorem nash_equilibrium_exists_of_potential [∀ i, Nonempty (S i)]
    (u : ι → (∀ j, S j) → ℝ) (P : (∀ j, S j) → ℝ)
    (hP : ∀ (i : ι) (p : ∀ j, S j) (s : S i),
      u i (Function.update p i s) - u i p = P (Function.update p i s) - P p) :
    ∃ x : ∀ j, S j → ℝ, IsNashEquilibrium u x := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (univ : Finset (∀ j, S j)) P
    ⟨Classical.arbitrary _, mem_univ _⟩
  refine ⟨pureProfile p, isNashEquilibrium_of_pure u (isMixed_pureProfile p) ?_⟩
  intro i s
  rw [devPayoff_pureProfile, payoff_pureProfile]
  have h1 := hP i p s
  have h2 : P (Function.update p i s) ≤ P p := hp _ (mem_univ _)
  linarith

/-- A concrete instance, showing the definitions are satisfiable: the two-player
coordination game on `Bool` (both players get `1` if they choose the same action and `0`
otherwise) has a Nash equilibrium. -/
theorem coordination_game_has_nash_equilibrium :
    ∃ x : (_ : Fin 2) → Bool → ℝ,
      IsNashEquilibrium (fun _ (p : (_ : Fin 2) → Bool) => if p 0 = p 1 then (1 : ℝ) else 0) x :=
  nash_equilibrium_exists_of_potential _ (fun p => if p 0 = p 1 then (1 : ℝ) else 0)
    (fun _ _ _ => rfl)

/-- A non-triviality check: `IsNashEquilibrium` is not vacuously true. In the one-player
game on `Bool` where action `true` pays `1` and action `false` pays `0`, playing `false`
is not an equilibrium. -/
theorem not_isNashEquilibrium_of_dominated :
    ¬ IsNashEquilibrium (fun (_ : Fin 1) (p : (_ : Fin 1) → Bool) => if p 0 then (1 : ℝ) else 0)
      (pureProfile (fun _ : Fin 1 => false)) := by
  intro h
  have hz := (isMixed_pureProfile (fun _ : Fin 1 => true)) 0
  have hle := h.2 0 (pureProfile (fun _ : Fin 1 => true) 0) hz
  have heq : Function.update (pureProfile (fun _ : Fin 1 => false)) 0
      (pureProfile (fun _ : Fin 1 => true) 0) = pureProfile (fun _ : Fin 1 => true) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  rw [heq, payoff_pureProfile, payoff_pureProfile] at hle
  norm_num at hle

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

