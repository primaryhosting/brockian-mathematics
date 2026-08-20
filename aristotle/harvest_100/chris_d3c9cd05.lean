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
def IsPureNashEquilibrium (g : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : Prop :=
  ∀ (i : ι) (a : S i), g i (Function.update s i a) ≤ g i s

/-- `P` is an exact potential for the game `g` (Monderer–Shapley): every unilateral
deviation changes the deviating player's payoff exactly as it changes `P`. -/
def IsPotential (g : ι → (∀ i, S i) → ℝ) (P : (∀ i, S i) → ℝ) : Prop :=
  ∀ (i : ι) (s : ∀ i, S i) (a : S i),
    g i (Function.update s i a) - g i s = P (Function.update s i a) - P s

end Defs

/-- **Brouwer's fixed point theorem**, as a hypothesis: every continuous self-map of a
nonempty compact convex subset of a finite-dimensional real normed space has a fixed
point.  (This form is the standard consequence of Brouwer's theorem for balls; it is not
currently available in Mathlib, so the general existence theorem below is stated as a
Lean-checked reduction to it.) -/
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
def diracProfile (s : ∀ i, S i) : ∀ i, S i → ℝ := fun i => pureStrat (s i)

theorem diracProfile_mem (s : ∀ i, S i) : diracProfile s ∈ MixedProfiles S :=
  fun i => pureStrat_mem_stdSimplex (s i)

theorem prod_diracProfile (s t : ∀ i, S i) :
    (∏ j, diracProfile s j (t j)) = if t = s then (1 : ℝ) else 0 := by
  by_cases h : t = s
  · subst h
    simp [diracProfile, pureStrat]
  · rw [if_neg h]
    obtain ⟨j, hj⟩ : ∃ j, t j ≠ s j := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp [diracProfile, pureStrat, hj]

theorem expectedPayoff_diracProfile (i : ι) (s : ∀ i, S i) :
    expectedPayoff g i (diracProfile s) = g i s := by
  unfold expectedPayoff
  rw [Finset.sum_congr rfl fun t _ => by rw [prod_diracProfile s t]]
  simp

theorem deviationPayoff_diracProfile (i : ι) (s : ∀ i, S i) (a : S i) :
    deviationPayoff g i (diracProfile s) a = g i (Function.update s i a) := by
  have h : Function.update (diracProfile s) i (pureStrat a)
      = diracProfile (Function.update s i a) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [diracProfile]
    · simp [diracProfile, Function.update_of_ne hj]
  rw [deviationPayoff, h, expectedPayoff_diracProfile]

/-- A pure Nash equilibrium gives a mixed Nash equilibrium. -/
theorem isNashEquilibrium_diracProfile {s : ∀ i, S i} (hs : IsPureNashEquilibrium g s) :
    IsNashEquilibrium g (diracProfile s) := by
  rw [isNashEquilibrium_iff (diracProfile_mem s)]
  intro i a
  rw [deviationPayoff_diracProfile, expectedPayoff_diracProfile]
  exact hs i a

/-- **Unconditional case: potential games.** A finite game admitting an exact potential has a
pure Nash equilibrium, namely any maximizer of the potential. -/
theorem pure_nash_equilibrium_exists_of_potential {P : (∀ i, S i) → ℝ} (hP : IsPotential g P) :
    ∃ s, IsPureNashEquilibrium g s := by
  obtain ⟨s, hs⟩ := Finite.exists_max (fun s : (∀ i, S i) => P s)
  refine ⟨s, fun i a => ?_⟩
  have hPle : P (Function.update s i a) ≤ P s := hs (Function.update s i a)
  have := hP i s a
  linarith

/-- **Unconditional case: potential games** have mixed-strategy Nash equilibria (no appeal to
Brouwer's theorem). -/
theorem nash_equilibrium_exists_of_potential {P : (∀ i, S i) → ℝ} (hP : IsPotential g P) :
    ∃ x, IsNashEquilibrium g x := by
  obtain ⟨s, hs⟩ := pure_nash_equilibrium_exists_of_potential hP
  exact ⟨diracProfile s, isNashEquilibrium_diracProfile hs⟩

end Unconditional

end Frontier

import Mathlib

/-!
# The minimax theorem for finite two-player zero-sum games

This file proves, unconditionally (no appeal to Brouwer's fixed point theorem), von Neumann's
minimax theorem: every finite two-player zero-sum game has a saddle point, i.e. a pair of
optimal mixed strategies.  Such a saddle point is exactly a mixed-strategy Nash equilibrium of
the zero-sum game, so this is an unconditional special case of Nash's theorem.

The proof goes through a theorem of the alternative (Ville's theorem), obtained from the
Hahn–Banach separation theorem for a compact convex set and a closed convex set.
-/

open scoped BigOperators

namespace Frontier

section Matrix

variable {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-- Payoff to the row player when they use the mixed strategy `p` and the column player uses
the pure strategy `n`. -/
def colPayoff (A : M → N → ℝ) (p : M → ℝ) (n : N) : ℝ := ∑ m, p m * A m n

/-- Payoff to the row player when they use the pure strategy `m` and the column player uses
the mixed strategy `q`. -/
def rowPayoff (A : M → N → ℝ) (q : N → ℝ) (m : M) : ℝ := ∑ n, q n * A m n

/-- Expected payoff to the row player in the matrix game `A` under mixed strategies `p`, `q`. -/
def matrixPayoff (A : M → N → ℝ) (p : M → ℝ) (q : N → ℝ) : ℝ := ∑ m, ∑ n, p m * q n * A m n

theorem matrixPayoff_eq_sum_row (A : M → N → ℝ) (p : M → ℝ) (q : N → ℝ) :
    matrixPayoff A p q = ∑ m, p m * rowPayoff A q m := by
  simp only [matrixPayoff, rowPayoff, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring

theorem matrixPayoff_eq_sum_col (A : M → N → ℝ) (p : M → ℝ) (q : N → ℝ) :
    matrixPayoff A p q = ∑ n, q n * colPayoff A p n := by
  simp only [matrixPayoff, colPayoff, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring

theorem continuous_colPayoff (A : M → N → ℝ) (n : N) :
    Continuous fun p : M → ℝ => colPayoff A p n :=
  continuous_finset_sum _ fun m _ => (continuous_apply m).mul continuous_const

theorem continuous_rowPayoff (A : M → N → ℝ) (m : M) :
    Continuous fun q : N → ℝ => rowPayoff A q m :=
  continuous_finset_sum _ fun n _ => (continuous_apply n).mul continuous_const

theorem colPayoff_sub_const {A : M → N → ℝ} {p : M → ℝ} (hp : p ∈ stdSimplex ℝ M) (c : ℝ)
    (n : N) : colPayoff (fun m n => A m n - c) p n = colPayoff A p n - c := by
  simp only [colPayoff, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem rowPayoff_sub_const {A : M → N → ℝ} {q : N → ℝ} (hq : q ∈ stdSimplex ℝ N) (c : ℝ)
    (m : M) : rowPayoff (fun m n => A m n - c) q m = rowPayoff A q m - c := by
  simp only [rowPayoff, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]

theorem colPayoff_pureStrat (A : M → N → ℝ) (m : M) (n : N) :
    colPayoff A (fun m' => if m = m' then 1 else 0) n = A m n := by
  simp [colPayoff]

/-- **Ville's theorem of the alternative.** For any real matrix `A`, either the row player has
a mixed strategy guaranteeing a nonnegative payoff against every column, or the column player
has a mixed strategy guaranteeing a strictly negative payoff against every row. -/
theorem exists_col_nonneg_or_row_neg [Nonempty M] (A : M → N → ℝ) :
    (∃ p ∈ stdSimplex ℝ M, ∀ n, 0 ≤ colPayoff A p n) ∨
      (∃ q ∈ stdSimplex ℝ N, ∀ m, rowPayoff A q m < 0) := by
  by_cases hcase : ∃ p ∈ stdSimplex ℝ M, ∀ n, 0 ≤ colPayoff A p n
  · exact Or.inl hcase
  right
  push_neg at hcase
  -- the linear map sending a mixed row strategy to its vector of payoffs against pure columns
  let L : (M → ℝ) →ₗ[ℝ] (N → ℝ) :=
    { toFun := fun p => colPayoff A p
      map_add' := by
        intro p p'
        funext n
        simp only [colPayoff, Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro c p
        funext n
        simp only [colPayoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring }
  set K : Set (N → ℝ) := L '' (stdSimplex ℝ M) with hKdef
  have hKc : IsCompact K :=
    (isCompact_stdSimplex M).image (continuous_pi fun n => continuous_colPayoff A n)
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ M).linear_image L
  set T : Set (N → ℝ) := Set.univ.pi fun _ : N => Set.Ici (0 : ℝ) with hTdef
  have hTconv : Convex ℝ T := convex_pi fun n _ => convex_Ici 0
  have hTclosed : IsClosed T := isClosed_set_pi fun n _ => isClosed_Ici
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ hyT
    obtain ⟨n, hn⟩ := hcase p hp
    have : (0 : ℝ) ≤ colPayoff A p n := by
      simpa using (Set.mem_univ_pi.1 hyT n)
    linarith
  obtain ⟨f, u, v, hfK, huv, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKc hTconv hTclosed hdisj
  set c : N → ℝ := fun n => f (Pi.single n 1 : N → ℝ) with hc
  have hf0 : f 0 = 0 := map_zero f
  have hv0 : v < 0 := by
    have h0T : (0 : N → ℝ) ∈ T := by
      refine Set.mem_univ_pi.2 fun n => ?_
      simp
    have := hfT 0 h0T
    rwa [hf0] at this
  have hcnn : ∀ n, 0 ≤ c n := by
    intro n
    by_contra hneg
    push_neg at hneg
    set t : ℝ := (v - 1) / c n with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg (by linarith) hneg
    have hmem : t • (Pi.single n 1 : N → ℝ) ∈ T := by
      refine Set.mem_univ_pi.2 fun n' => ?_
      by_cases h : n = n' <;> simp [h, htpos.le]
    have := hfT _ hmem
    rw [map_smul] at this
    have hcn : t * c n = v - 1 := by
      have hne0 : c n ≠ 0 := ne_of_lt hneg
      rw [ht]
      exact div_mul_cancel₀ _ hne0
    simp only [smul_eq_mul] at this
    rw [hcn] at this
    linarith
  have hfy : ∀ y : N → ℝ, f y = ∑ n, y n * c n := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsingle : (Pi.single n (y n) : N → ℝ) = y n • (Pi.single n 1 : N → ℝ) := by
      funext n'
      by_cases h : n = n' <;> simp [Pi.single_apply, h]
    rw [hsingle, map_smul]
    simp [hc]
  -- the pure strategies of the row player give points of `K`
  have hpure : ∀ m : M, (fun n => A m n) ∈ K := by
    intro m
    refine ⟨fun m' => if m = m' then 1 else 0, ite_eq_mem_stdSimplex ℝ m, ?_⟩
    funext n
    exact colPayoff_pureStrat A m n
  have hnegrow : ∀ m : M, ∑ n, A m n * c n < 0 := by
    intro m
    have h1 := hfK _ (hpure m)
    rw [hfy] at h1
    linarith
  have hSpos : 0 < ∑ n, c n := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun n _ => hcnn n) with h | h
    · exact h
    · exfalso
      have hzero : ∀ n, c n = 0 := by
        intro n
        have := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => hcnn n).1 h.symm n (Finset.mem_univ n)
        exact this
      have := hnegrow (Classical.arbitrary M)
      rw [Finset.sum_congr rfl fun n _ => by rw [hzero n, mul_zero]] at this
      simp at this
  refine ⟨fun n => c n / ∑ n', c n', ⟨fun n => div_nonneg (hcnn n) hSpos.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hSpos)]
  · intro m
    have hrow : rowPayoff A (fun n => c n / ∑ n', c n') m = (∑ n, A m n * c n) / ∑ n', c n' := by
      simp only [rowPayoff, Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hrow]
    exact div_neg_of_neg_of_pos (hnegrow m) hSpos

/-- The row player has an optimal (maximin) mixed strategy. -/
theorem exists_maximin [Nonempty M] [Nonempty N] (A : M → N → ℝ) :
    ∃ p ∈ stdSimplex ℝ M, ∃ v : ℝ, (∀ n, v ≤ colPayoff A p n) ∧
      ∀ p' ∈ stdSimplex ℝ M, ∃ n, colPayoff A p' n ≤ v := by
  have hne : (Finset.univ : Finset N).Nonempty := Finset.univ_nonempty
  set F : (M → ℝ) → ℝ :=
    Finset.univ.inf' hne (fun n => fun p : M → ℝ => colPayoff A p n) with hF
  have hFc : Continuous F := Continuous.finset_inf' hne fun n _ => continuous_colPayoff A n
  have hFapply : ∀ p : M → ℝ, F p = Finset.univ.inf' hne fun n => colPayoff A p n := by
    intro p
    rw [hF, Finset.inf'_apply]
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_stdSimplex M).exists_isMaxOn
      ⟨_, ite_eq_mem_stdSimplex ℝ (Classical.arbitrary M)⟩ hFc.continuousOn
  refine ⟨p, hp, F p, fun n => ?_, fun p' hp' => ?_⟩
  · rw [hFapply p]
    exact Finset.inf'_le _ (Finset.mem_univ n)
  · obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_inf' hne fun n => colPayoff A p' n
    refine ⟨n, ?_⟩
    have h1 : F p' ≤ F p := hmax hp'
    rw [hFapply p'] at h1
    rw [← hn]
    exact h1

/-- The column player has an optimal (minimax) mixed strategy. -/
theorem exists_minimax [Nonempty M] [Nonempty N] (A : M → N → ℝ) :
    ∃ q ∈ stdSimplex ℝ N, ∃ w : ℝ, (∀ m, rowPayoff A q m ≤ w) ∧
      ∀ q' ∈ stdSimplex ℝ N, ∃ m, w ≤ rowPayoff A q' m := by
  have hne : (Finset.univ : Finset M).Nonempty := Finset.univ_nonempty
  set G : (N → ℝ) → ℝ :=
    Finset.univ.sup' hne (fun m => fun q : N → ℝ => rowPayoff A q m) with hG
  have hGc : Continuous G := Continuous.finset_sup' hne fun m _ => continuous_rowPayoff A m
  have hGapply : ∀ q : N → ℝ, G q = Finset.univ.sup' hne fun m => rowPayoff A q m := by
    intro q
    rw [hG, Finset.sup'_apply]
  obtain ⟨q, hq, hmin⟩ :=
    (isCompact_stdSimplex N).exists_isMinOn
      ⟨_, ite_eq_mem_stdSimplex ℝ (Classical.arbitrary N)⟩ hGc.continuousOn
  refine ⟨q, hq, G q, fun m => ?_, fun q' hq' => ?_⟩
  · rw [hGapply q]
    exact Finset.le_sup' _ (Finset.mem_univ m)
  · obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' hne fun m => rowPayoff A q' m
    refine ⟨m, ?_⟩
    have h1 : G q ≤ G q' := hmin hq'
    rw [hGapply q'] at h1
    rw [← hm]
    exact h1

/-- **von Neumann's minimax theorem**: every finite two-player zero-sum game has a saddle point
in mixed strategies. Unconditional: no fixed point theorem is used. -/
theorem exists_saddle_point [Nonempty M] [Nonempty N] (A : M → N → ℝ) :
    ∃ p ∈ stdSimplex ℝ M, ∃ q ∈ stdSimplex ℝ N,
      ∀ p' ∈ stdSimplex ℝ M, ∀ q' ∈ stdSimplex ℝ N,
        matrixPayoff A p' q ≤ matrixPayoff A p q ∧ matrixPayoff A p q ≤ matrixPayoff A p q' := by
  obtain ⟨p, hp, v, hv1, hv2⟩ := exists_maximin A
  obtain ⟨q, hq, w, hw1, hw2⟩ := exists_minimax A
  have hwv : w ≤ v := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rcases exists_col_nonneg_or_row_neg (fun m n => A m n - (v + ε)) with
      ⟨p', hp', hcol⟩ | ⟨q', hq', hrow⟩
    · exfalso
      obtain ⟨n, hn⟩ := hv2 p' hp'
      have h1 := hcol n
      rw [colPayoff_sub_const hp' (v + ε) n] at h1
      linarith
    · obtain ⟨m, hm⟩ := hw2 q' hq'
      have h1 := hrow m
      rw [rowPayoff_sub_const hq' (v + ε) m] at h1
      linarith
  have hle : ∀ p' ∈ stdSimplex ℝ M, matrixPayoff A p' q ≤ v := by
    intro p' hp'
    rw [matrixPayoff_eq_sum_row]
    calc ∑ m, p' m * rowPayoff A q m
        ≤ ∑ m, p' m * v :=
          Finset.sum_le_sum fun m _ =>
            mul_le_mul_of_nonneg_left (le_trans (hw1 m) hwv) (hp'.1 m)
      _ = v := by rw [← Finset.sum_mul, hp'.2, one_mul]
  have hge : ∀ q' ∈ stdSimplex ℝ N, v ≤ matrixPayoff A p q' := by
    intro q' hq'
    rw [matrixPayoff_eq_sum_col]
    calc v = ∑ n, q' n * v := by rw [← Finset.sum_mul, hq'.2, one_mul]
      _ ≤ ∑ n, q' n * colPayoff A p n :=
          Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hv1 n) (hq'.1 n)
  have heq : matrixPayoff A p q = v := le_antisymm (hle p hp) (hge q hq)
  refine ⟨p, hp, q, hq, fun p' hp' q' hq' => ⟨?_, ?_⟩⟩
  · rw [heq]
    exact hle p' hp'
  · rw [heq]
    exact hge q' hq' 

end Matrix

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

