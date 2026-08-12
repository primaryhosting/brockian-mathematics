/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/
noncomputable def payoffVec (A : m → n → ℝ) (y : n → ℝ) : m → ℝ := fun i => ∑ j, y j * A i j

/-- The vector of expected payoffs to the row player, as a function of the column played. -/
noncomputable def colPayoff (A : m → n → ℝ) (x : m → ℝ) : n → ℝ := fun j => ∑ i, x i * A i j

/-- The expected payoff to the row player of the mixed strategy pair `(x, y)`. -/
noncomputable def bilin (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * y j * A i j

omit [DecidableEq m] [DecidableEq n] in
theorem bilin_eq_row (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilin A x y = ∑ i, x i * payoffVec A y i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [payoffVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq m] [DecidableEq n] in
theorem bilin_eq_col (A : m → n → ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilin A x y = ∑ j, y j * colPayoff A x j := by
  rw [bilin, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colPayoff, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype m] [DecidableEq m] in
theorem payoffVec_pureVec (A : m → n → ℝ) (j : n) (i : m) :
    payoffVec A (pureVec j) i = A i j := by
  simp [payoffVec, pureVec]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem continuous_payoffVec (A : m → n → ℝ) : Continuous (payoffVec A) := by
  refine continuous_pi fun i => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_apply j).mul continuous_const

/-! ### Representation of continuous linear functionals on `m → ℝ` -/

theorem strongDual_repr (f : StrongDual ℝ (m → ℝ)) (z : m → ℝ) :
    f z = ∑ i, z i * f (Pi.single i 1) := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : m → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [smul_eq_mul]

/-! ### The theorem of the alternative -/

/-- `payoffVec A` as a linear map. -/
noncomputable def payoffMap (A : m → n → ℝ) : (n → ℝ) →ₗ[ℝ] (m → ℝ) where
  toFun := payoffVec A
  map_add' y₁ y₂ := by
    funext i
    simp [payoffVec, add_mul, Finset.sum_add_distrib]
  map_smul' c y := by
    funext i
    simp [payoffVec, Finset.mul_sum, mul_assoc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem coe_payoffMap (A : m → n → ℝ) : ⇑(payoffMap A) = payoffVec A := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The image of the simplex under `payoffVec` is convex. -/
theorem convex_payoffVec_image (A : m → n → ℝ) :
    Convex ℝ (payoffVec A '' stdSimplex ℝ n) := by
  rw [← coe_payoffMap]
  exact (convex_stdSimplex ℝ n).linear_image (payoffMap A)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem isCompact_payoffVec_image (A : m → n → ℝ) :
    IsCompact (payoffVec A '' stdSimplex ℝ n) :=
  (isCompact_stdSimplex n).image (continuous_payoffVec A)

omit [Fintype m] [DecidableEq m] in
/-- The nonpositive orthant is closed. -/
theorem isClosed_nonpos : IsClosed {z : m → ℝ | ∀ i, z i ≤ 0} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const

omit [Fintype m] [DecidableEq m] in
theorem convex_nonpos : Convex ℝ {z : m → ℝ | ∀ i, z i ≤ 0} := by
  intro x hx y hy a b ha hb _ i
  have h1 : ((a • x + b • y) : m → ℝ) i = a * x i + b * y i := rfl
  rw [h1]
  have hxi := hx i
  have hyi := hy i
  nlinarith

theorem stdSimplex_nonempty (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    (stdSimplex ℝ α).Nonempty :=
  ⟨pureVec (Classical.arbitrary α), pureVec_mem_stdSimplex _⟩

/-- **Theorem of the alternative.** Either the column player can guarantee a nonpositive
payoff to the row player, or the row player has a mixed strategy which is strictly
profitable against every column. -/
theorem exists_alternative [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    (∃ y ∈ stdSimplex ℝ n, ∀ i, payoffVec A y i ≤ 0) ∨
      (∃ x ∈ stdSimplex ℝ m, ∀ j, 0 < colPayoff A x j) := by
  by_cases hK : ∃ y ∈ stdSimplex ℝ n, ∀ i, payoffVec A y i ≤ 0
  · exact Or.inl hK
  right
  push_neg at hK
  have hdisj : Disjoint (payoffVec A '' stdSimplex ℝ n) {z : m → ℝ | ∀ i, z i ≤ 0} := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hz
    obtain ⟨i, hi⟩ := hK y hy
    exact absurd (hz i) (not_le.2 hi)
  obtain ⟨f, u, v, hKu, huv, hNv⟩ := geometric_hahn_banach_compact_closed
    (convex_payoffVec_image A) (isCompact_payoffVec_image A) convex_nonpos isClosed_nonpos hdisj
  obtain ⟨c, hcdef⟩ : ∃ c : m → ℝ, ∀ i, c i = f (Pi.single i 1) := ⟨_, fun _ => rfl⟩
  have hrep : ∀ z : m → ℝ, f z = ∑ i, z i * c i := by
    intro z
    rw [strongDual_repr f]
    exact Finset.sum_congr rfl fun i _ => by rw [hcdef i]
  -- `v < 0`, since `0` lies in the nonpositive orthant
  have hv : v < 0 := by
    have : v < f 0 := hNv 0 (by intro i; simp)
    simpa using this
  -- all coefficients of `f` are nonpositive
  have hcnonpos : ∀ i, c i ≤ 0 := by
    intro i
    by_contra hci
    push_neg at hci
    have hcne : c i ≠ 0 := ne_of_gt hci
    set t : ℝ := (1 - v) / c i with ht
    have htpos : 0 < t := div_pos (by linarith) hci
    have hval : t * c i = 1 - v := by
      rw [ht]; field_simp
    have hmem : (fun k => if k = i then -t else 0) ∈ {z : m → ℝ | ∀ k, z k ≤ 0} := by
      intro k
      by_cases h : k = i <;> simp [h]
      linarith
    have hlt := hNv _ hmem
    rw [hrep] at hlt
    have hsum : ∑ k, (if k = i then -t else 0) * c k = -t * c i := by
      simp [ite_mul]
    rw [hsum] at hlt
    nlinarith
  -- `f` is strictly negative on the (nonempty) image of the simplex
  have hKneg : ∀ w ∈ payoffVec A '' stdSimplex ℝ n, f w < 0 := fun w hw =>
    lt_trans (hKu w hw) (by linarith)
  obtain ⟨y0, hy0⟩ := stdSimplex_nonempty n
  have hw0 : f (payoffVec A y0) < 0 := hKneg _ ⟨y0, hy0, rfl⟩
  -- hence some coefficient is strictly negative
  have hexists : ∃ i, c i < 0 := by
    by_contra hall
    push_neg at hall
    have hzero : ∀ i, c i = 0 := fun i => le_antisymm (hcnonpos i) (hall i)
    have : f (payoffVec A y0) = 0 := by
      rw [hrep]
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]
    linarith
  obtain ⟨i0, hi0⟩ := hexists
  set D : ℝ := ∑ i, -c i with hD
  have hDpos : 0 < D := by
    refine Finset.sum_pos' (fun i _ => by linarith [hcnonpos i]) ⟨i0, Finset.mem_univ _, ?_⟩
    linarith
  refine ⟨fun i => (-c i) / D, ⟨fun i => div_nonneg (by linarith [hcnonpos i]) hDpos.le, ?_⟩,
    ?_⟩
  · rw [← Finset.sum_div, ← hD]
    exact div_self (ne_of_gt hDpos)
  · intro j
    have hfj : f (payoffVec A (pureVec j)) < 0 := hKneg _ ⟨pureVec j, pureVec_mem_stdSimplex j, rfl⟩
    have hrepr : f (payoffVec A (pureVec j)) = ∑ i, A i j * c i := by
      rw [hrep]
      exact Finset.sum_congr rfl fun i _ => by rw [payoffVec_pureVec]
    have hsum : colPayoff A (fun i => (-c i) / D) j = (∑ i, -(A i j * c i)) / D := by
      rw [colPayoff, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    rw [hsum]
    apply div_pos _ hDpos
    have : ∑ i, -(A i j * c i) = -(∑ i, A i j * c i) := by
      rw [← Finset.sum_neg_distrib]
    rw [this, ← hrepr]
    linarith

/-! ### The value of the game -/

/-- The security level of the row player's mixed strategy `x`: the worst payoff over all
columns. -/
noncomputable def rowValue [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (colPayoff A x)

omit [DecidableEq m] [DecidableEq n] in
theorem rowValue_le [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) (j : n) :
    rowValue A x ≤ colPayoff A x j :=
  Finset.inf'_le _ (Finset.mem_univ j)

omit [DecidableEq m] [DecidableEq n] in
theorem le_rowValue [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) {c : ℝ}
    (h : ∀ j, c ≤ colPayoff A x j) : c ≤ rowValue A x :=
  Finset.le_inf' _ _ fun j _ => h j

omit [DecidableEq m] [DecidableEq n] in
theorem exists_rowValue_eq [Nonempty n] (A : m → n → ℝ) (x : m → ℝ) :
    ∃ j, rowValue A x = colPayoff A x j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := n)) (colPayoff A x)
  exact ⟨j, hj⟩

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem continuous_colPayoff (A : m → n → ℝ) (j : n) :
    Continuous fun x : m → ℝ => colPayoff A x j :=
  continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const

omit [DecidableEq m] [DecidableEq n] in
theorem continuous_rowValue [Nonempty n] (A : m → n → ℝ) : Continuous (rowValue A) := by
  have : Continuous fun x : m → ℝ =>
      Finset.univ.inf' (Finset.univ_nonempty (α := n)) (fun j => colPayoff A x j) :=
    Continuous.finset_inf'_apply _ fun j _ => continuous_colPayoff A j
  exact this

omit [DecidableEq n] in
/-- The row player has an optimal (maximin) mixed strategy. -/
theorem exists_max_rowValue [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x ∈ stdSimplex ℝ m, ∀ x' ∈ stdSimplex ℝ m, rowValue A x' ≤ rowValue A x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex m).exists_isMaxOn (stdSimplex_nonempty m)
    (continuous_rowValue A).continuousOn
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

/-! ### The minimax theorem -/

/-- **von Neumann's minimax theorem** / existence of a saddle point: every two player
zero sum finite game has a mixed strategy Nash equilibrium.  This is proved
unconditionally, without Brouwer's fixed point theorem. -/
theorem exists_saddle_point [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ x ∈ stdSimplex ℝ m, ∃ y ∈ stdSimplex ℝ n,
      (∀ x' ∈ stdSimplex ℝ m, bilin A x' y ≤ bilin A x y) ∧
      (∀ y' ∈ stdSimplex ℝ n, bilin A x y ≤ bilin A x y') := by
  obtain ⟨x, hx, hxmax⟩ := exists_max_rowValue A
  set v : ℝ := rowValue A x with hv
  set B : m → n → ℝ := fun i j => A i j - v with hB
  have halt := exists_alternative B
  -- the second alternative is impossible, by maximality of `x`
  have hnot : ¬ ∃ x' ∈ stdSimplex ℝ m, ∀ j, 0 < colPayoff B x' j := by
    rintro ⟨x', hx', hpos⟩
    have hcol : ∀ j, colPayoff B x' j = colPayoff A x' j - v := by
      intro j
      have : colPayoff B x' j = ∑ i, (x' i * A i j - x' i * v) := by
        refine Finset.sum_congr rfl fun i _ => by simp [hB]; ring
      rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hx'.2, one_mul]
      rfl
    obtain ⟨j0, hj0⟩ := exists_rowValue_eq A x'
    have h1 : v < colPayoff A x' j0 := by
      have := hpos j0
      rw [hcol j0] at this
      linarith
    have h2 := hxmax x' hx'
    rw [← hj0] at h1
    linarith
  obtain ⟨y, hy, hyle⟩ := halt.resolve_right hnot
  have hyA : ∀ i, payoffVec A y i ≤ v := by
    intro i
    have h := hyle i
    have : payoffVec B y i = payoffVec A y i - v := by
      have hexp : payoffVec B y i = ∑ j, (y j * A i j - y j * v) := by
        refine Finset.sum_congr rfl fun j _ => by simp [hB]; ring
      rw [hexp, Finset.sum_sub_distrib, ← Finset.sum_mul, hy.2, one_mul]
      rfl
    rw [this] at h
    linarith
  -- the row player cannot get more than `v` against `y`
  have hrow : ∀ x' ∈ stdSimplex ℝ m, bilin A x' y ≤ v := by
    intro x' hx'
    rw [bilin_eq_row]
    calc ∑ i, x' i * payoffVec A y i ≤ ∑ i, x' i * v :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyA i) (hx'.1 i)
      _ = v := by rw [← Finset.sum_mul, hx'.2, one_mul]
  -- the column player cannot get more than `-v` against `x`
  have hcol : ∀ y' ∈ stdSimplex ℝ n, v ≤ bilin A x y' := by
    intro y' hy'
    rw [bilin_eq_col]
    calc v = ∑ j, y' j * v := by rw [← Finset.sum_mul, hy'.2, one_mul]
      _ ≤ ∑ j, y' j * colPayoff A x j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (rowValue_le A x j) (hy'.1 j)
  have hval : bilin A x y = v := le_antisymm (hrow x hx) (hcol y hy)
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · intro x' hx'
    rw [hval]
    exact hrow x' hx'
  · intro y' hy'
    rw [hval]
    exact hcol y' hy'

end Frontier

/-
Bridging the minimax theorem into the general finite game framework: a two player
zero sum finite game, viewed as a `FiniteGame` with player set `Bool`, has a mixed
strategy Nash equilibrium.  This is unconditional (no Brouwer hypothesis).
-/

import RequestProject.Minimax

/-!
# Two player zero sum games as finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The strategy sets of a two player game: the row player is `true`. -/
def twoStrat (m n : Type) : Bool → Type := fun b => cond b m n

instance instFintypeTwoStrat (b : Bool) : Fintype (twoStrat m n b) := by
  cases b
  · exact inferInstanceAs (Fintype n)
  · exact inferInstanceAs (Fintype m)

instance instDecidableEqTwoStrat (b : Bool) : DecidableEq (twoStrat m n b) := by
  cases b
  · exact inferInstanceAs (DecidableEq n)
  · exact inferInstanceAs (DecidableEq m)

instance instNonemptyTwoStrat [Nonempty m] [Nonempty n] (b : Bool) :
    Nonempty (twoStrat m n b) := by
  cases b
  · exact inferInstanceAs (Nonempty n)
  · exact inferInstanceAs (Nonempty m)

/-- A pure strategy profile of a two player game, built from the two components. -/
def twoProfile (i : m) (j : n) : (b : Bool) → twoStrat m n b :=
  fun b => match b with
    | true => i
    | false => j

/-- A mixed strategy profile of a two player game, built from the two components. -/
def twoMixed (x : m → ℝ) (y : n → ℝ) : (b : Bool) → twoStrat m n b → ℝ :=
  fun b => match b with
    | true => x
    | false => y

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem twoMixed_true (x : m → ℝ) (y : n → ℝ) : twoMixed x y true = x := rfl

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem twoMixed_false (x : m → ℝ) (y : n → ℝ) : twoMixed x y false = y := rfl

/-- Pure profiles of a two player game are just pairs. -/
def twoProfileEquiv (m n : Type) : ((b : Bool) → twoStrat m n b) ≃ m × n where
  toFun σ := (σ true, σ false)
  invFun p := twoProfile p.1 p.2
  left_inv σ := by
    funext b
    cases b <;> rfl
  right_inv p := rfl

omit [DecidableEq m] [DecidableEq n] in
/-- Summing over pure profiles of a two player game. -/
theorem sum_two_profile (f : ((b : Bool) → twoStrat m n b) → ℝ) :
    ∑ σ : ((b : Bool) → twoStrat m n b), f σ = ∑ i : m, ∑ j : n, f (twoProfile i j) := by
  have h1 : ∑ σ : ((b : Bool) → twoStrat m n b), f σ = ∑ p : m × n, f (twoProfile p.1 p.2) :=
    Fintype.sum_equiv (twoProfileEquiv m n) _ _ fun σ => by
      congr 1
      funext b
      cases b <;> rfl
  rw [h1, Fintype.sum_prod_type]

/-- The two player zero sum game with payoff matrix `A`: the row player `true` receives
`A i j` and the column player `false` receives `-A i j`. -/
def zeroSumGame (A : m → n → ℝ) : FiniteGame Bool (twoStrat m n) where
  payoff := fun b σ => cond b (A (σ true) (σ false)) (-(A (σ true) (σ false)))

omit [DecidableEq m] [DecidableEq n] in
theorem expectedPayoff_zeroSum_true (A : m → n → ℝ)
    (z : (b : Bool) → twoStrat m n b → ℝ) :
    expectedPayoff (zeroSumGame A) true z = bilin A (z true) (z false) := by
  rw [expectedPayoff, sum_two_profile, bilin]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  rfl

omit [DecidableEq m] [DecidableEq n] in
theorem expectedPayoff_zeroSum_false (A : m → n → ℝ)
    (z : (b : Bool) → twoStrat m n b → ℝ) :
    expectedPayoff (zeroSumGame A) false z = -bilin A (z true) (z false) := by
  rw [expectedPayoff, sum_two_profile, bilin, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.prod_bool]
  simp [zeroSumGame, twoProfile]

/-- **Unconditional Nash existence for two player zero sum finite games.**  No fixed
point theorem is needed: the equilibrium comes from the minimax theorem. -/
theorem nash_equilibrium_exists_zeroSum [Nonempty m] [Nonempty n] (A : m → n → ℝ) :
    ∃ z : (b : Bool) → twoStrat m n b → ℝ, IsNash (zeroSumGame A) z := by
  obtain ⟨x, hx, y, hy, hrow, hcol⟩ := exists_saddle_point A
  refine ⟨twoMixed x y, ?_⟩
  have hmix : IsMixed (twoMixed x y) := by
    intro b
    cases b
    · exact hy
    · exact hx
  rw [isNash_iff _ hmix]
  intro b
  cases b
  · -- the column player
    intro t
    rw [devPayoff, expectedPayoff_zeroSum_false, expectedPayoff_zeroSum_false]
    have h1 : (Function.update (twoMixed x y) false (pureVec t)) true = x := rfl
    have h2 : (Function.update (twoMixed x y) false (pureVec t)) false = pureVec t := by
      rw [Function.update_self]
    rw [h1, h2, twoMixed_true, twoMixed_false]
    have := hcol (pureVec t) (pureVec_mem_stdSimplex t)
    linarith
  · -- the row player
    intro s
    rw [devPayoff, expectedPayoff_zeroSum_true, expectedPayoff_zeroSum_true]
    have h1 : (Function.update (twoMixed x y) true (pureVec s)) true = pureVec s := by
      rw [Function.update_self]
    have h2 : (Function.update (twoMixed x y) true (pureVec s)) false = y := rfl
    rw [h1, h2, twoMixed_true, twoMixed_false]
    exact hrow (pureVec s) (pureVec_mem_stdSimplex s)

/-! ### A concrete example: matching pennies -/

/-- Matching pennies: the row player wins the penny iff the two coins agree. -/
def matchingPennies : Bool → Bool → ℝ := fun i j => if i = j then 1 else -1

/-- Matching pennies has no pure Nash equilibrium: the equilibrium below is genuinely
mixed. -/
theorem matchingPennies_no_pureNash :
    ¬ ∃ s : (b : Bool) → twoStrat Bool Bool b,
      IsPureNash (zeroSumGame matchingPennies) s := by
  rintro ⟨s, hs⟩
  by_cases h : (s true : Bool) = (s false : Bool)
  · have hdev := hs false (!(s false))
    simp [zeroSumGame, matchingPennies, h] at hdev
    linarith
  · have hdev := hs true (s false)
    simp [zeroSumGame, matchingPennies, h] at hdev
    linarith

/-- The uniform mixed strategy over a coin flip. -/
noncomputable def uniformBool : Bool → ℝ := fun _ => 1 / 2

theorem uniformBool_mem_stdSimplex : uniformBool ∈ stdSimplex ℝ Bool := by
  constructor
  · intro t
    norm_num [uniformBool]
  · norm_num [uniformBool, Fintype.sum_bool]

/-- In matching pennies, both players randomizing uniformly is a Nash equilibrium. -/
theorem matchingPennies_nash :
    IsNash (zeroSumGame matchingPennies) (twoMixed uniformBool uniformBool) := by
  have hmix : IsMixed (twoMixed uniformBool uniformBool) := by
    intro b
    cases b <;> exact uniformBool_mem_stdSimplex
  have hbilin : ∀ x : Bool → ℝ, bilin matchingPennies x uniformBool = 0 := by
    intro x
    simp [bilin, matchingPennies, uniformBool]
  have hbilin' : ∀ y : Bool → ℝ, bilin matchingPennies uniformBool y = 0 := by
    intro y
    simp [bilin, matchingPennies, uniformBool]
    ring
  rw [isNash_iff _ hmix]
  intro b s
  cases b
  · rw [devPayoff, expectedPayoff_zeroSum_false, expectedPayoff_zeroSum_false]
    have h1 : (Function.update (twoMixed uniformBool uniformBool)
        false (pureVec s)) true = uniformBool := rfl
    have h2 : (Function.update (twoMixed uniformBool uniformBool)
        false (pureVec s)) false = pureVec s := Function.update_self _ _ _
    rw [h1, h2, hbilin' (pureVec s), twoMixed_true, twoMixed_false, hbilin']
  · rw [devPayoff, expectedPayoff_zeroSum_true, expectedPayoff_zeroSum_true]
    have h1 : (Function.update (twoMixed uniformBool uniformBool)
        true (pureVec s)) true = pureVec s := Function.update_self _ _ _
    have h2 : (Function.update (twoMixed uniformBool uniformBool)
        true (pureVec s)) false = uniformBool := rfl
    rw [h1, h2, hbilin (pureVec s), twoMixed_true, twoMixed_false, hbilin]

end Frontier

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

namespace Frontier

/-- A finite game in normal form: a finite set of players `ι`, a finite set of
pure strategies `S i` for each player, and a real payoff for each player at each pure
strategy profile. -/
structure FiniteGame (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ i, Fintype (S i)] where
  payoff : ι → ((i : ι) → S i) → ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A mixed strategy profile: each player's mixed strategy lies in the standard simplex. -/
def IsMixed (x : (i : ι) → S i → ℝ) : Prop := ∀ i, x i ∈ stdSimplex ℝ (S i)

/-- The pure strategy `s`, viewed as a mixed strategy (a Dirac vector). -/
def pureVec {α : Type} [DecidableEq α] (s : α) : α → ℝ := fun t => if t = s then 1 else 0

/-- The expected payoff of player `i` under a mixed strategy profile `x`. -/
noncomputable def expectedPayoff (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) : ℝ :=
  ∑ s : ((i : ι) → S i), (∏ j, x j (s j)) * G.payoff i s

/-- The expected payoff of player `i` when he deviates to the pure strategy `s`. -/
noncomputable def devPayoff (G : FiniteGame ι S) (i : ι) (s : S i)
    (x : (i : ι) → S i → ℝ) : ℝ :=
  expectedPayoff G i (Function.update x i (pureVec s))

/-- `x` is a (mixed strategy) Nash equilibrium: it is a mixed profile and no player can
strictly improve his expected payoff by unilaterally switching to another mixed strategy. -/
def IsNash (G : FiniteGame ι S) (x : (i : ι) → S i → ℝ) : Prop :=
  IsMixed x ∧ ∀ i, ∀ y ∈ stdSimplex ℝ (S i),
    expectedPayoff G i (Function.update x i y) ≤ expectedPayoff G i x

/-- Brouwer's fixed point theorem, as a hypothesis: every continuous self-map of a
nonempty compact convex subset of a finite dimensional real normed space has a fixed
point.  (This statement is not available in Mathlib, so the main theorem below is a
Lean-checked reduction of Nash's theorem to it.) -/
def BrouwerProperty : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E), K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : E → E, Continuous f → Set.MapsTo f K K → ∃ x ∈ K, f x = x

/-! ### Basic facts about Dirac vectors -/

theorem pureVec_mem_stdSimplex {α : Type} [Fintype α] [DecidableEq α] (s : α) :
    pureVec s ∈ stdSimplex ℝ α := by
  constructor
  · intro t
    by_cases h : t = s <;> simp [pureVec, h]
  · simp [pureVec]

/-! ### Multilinearity of the expected payoff -/

omit [(i : ι) → Fintype (S i)] [(i : ι) → DecidableEq (S i)] in
/-- Splitting the product defining the expected payoff along player `i`'s coordinate. -/
theorem prod_update_apply (i : ι) (x : (i : ι) → S i → ℝ) (v : S i → ℝ)
    (σ : (i : ι) → S i) :
    ∏ j, (Function.update x i v) j (σ j)
      = v (σ i) * ∏ j ∈ Finset.univ.erase i, x j (σ j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => Function.update x i v j (σ j))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The deviation payoff does not depend on player `i`'s own mixed strategy. -/
theorem devPayoff_update (G : FiniteGame ι S) (i : ι) (s : S i)
    (x : (i : ι) → S i → ℝ) (y : S i → ℝ) :
    devPayoff G i s (Function.update x i y) = devPayoff G i s x := by
  simp [devPayoff, Function.update_idem]

/-- Expanding the expected payoff along player `i`'s own mixed strategy. -/
theorem expectedPayoff_eq_sum (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) :
    expectedPayoff G i x = ∑ s : S i, x i s * devPayoff G i s x := by
  simp only [expectedPayoff, devPayoff, Finset.mul_sum, prod_update_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j (σ j)) (Finset.mem_univ i)]
  simp only [pureVec]
  rw [Finset.sum_eq_single (σ i)]
  · simp; ring
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A mixed profile is a Nash equilibrium iff no player can improve by a *pure* deviation. -/
theorem isNash_iff (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x) :
    IsNash G x ↔ ∀ i, ∀ s : S i, devPayoff G i s x ≤ expectedPayoff G i x := by
  constructor
  · intro hN i s
    exact hN.2 i (pureVec s) (pureVec_mem_stdSimplex s)
  · intro h
    refine ⟨hx, fun i y hy => ?_⟩
    have h1 : expectedPayoff G i (Function.update x i y)
        = ∑ s : S i, y s * devPayoff G i s x := by
      rw [expectedPayoff_eq_sum G i (Function.update x i y)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Function.update_self, devPayoff_update]
    have h2 : ∑ s : S i, y s * devPayoff G i s x
        ≤ ∑ s : S i, y s * expectedPayoff G i x := by
      refine Finset.sum_le_sum fun s _ => ?_
      exact mul_le_mul_of_nonneg_left (h i s) (hy.1 s)
    have h3 : ∑ s : S i, y s * expectedPayoff G i x = expectedPayoff G i x := by
      rw [← Finset.sum_mul, hy.2, one_mul]
    rw [h1]
    exact h2.trans_eq h3

/-! ### Continuity -/

omit [(i : ι) → DecidableEq (S i)] in
theorem continuous_expectedPayoff (G : FiniteGame ι S) (i : ι) :
    Continuous fun x : (i : ι) → S i → ℝ => expectedPayoff G i x := by
  unfold expectedPayoff
  refine continuous_finset_sum _ fun σ _ => Continuous.mul ?_ continuous_const
  exact continuous_finset_prod _ fun j _ => (continuous_apply (σ j)).comp (continuous_apply j)

omit [Fintype ι] [(i : ι) → Fintype (S i)] [(i : ι) → DecidableEq (S i)] in
theorem continuous_update (i : ι) (v : S i → ℝ) :
    Continuous fun x : (i : ι) → S i → ℝ => Function.update x i v := by
  refine continuous_pi fun j => ?_
  by_cases h : j = i
  · subst h
    simpa [Function.update_self] using (continuous_const : Continuous
      fun _ : (i : ι) → S i → ℝ => v)
  · simpa [Function.update_of_ne h] using (continuous_apply j :
      Continuous fun x : (i : ι) → S i → ℝ => x j)

theorem continuous_devPayoff (G : FiniteGame ι S) (i : ι) (s : S i) :
    Continuous fun x : (i : ι) → S i → ℝ => devPayoff G i s x :=
  (continuous_expectedPayoff G i).comp (continuous_update i (pureVec s))

/-! ### Nash's map -/

/-- The "regret" of player `i` for the pure strategy `s` at the profile `x`. -/
noncomputable def gain (G : FiniteGame ι S) (i : ι) (s : S i) (x : (i : ι) → S i → ℝ) : ℝ :=
  max 0 (devPayoff G i s x - expectedPayoff G i x)

/-- Nash's map: add the regrets and renormalize. -/
noncomputable def nashMap (G : FiniteGame ι S) (x : (i : ι) → S i → ℝ) :
    (i : ι) → S i → ℝ :=
  fun i s => (x i s + gain G i s x) / (1 + ∑ t : S i, gain G i t x)

theorem gain_nonneg (G : FiniteGame ι S) (i : ι) (s : S i) (x : (i : ι) → S i → ℝ) :
    0 ≤ gain G i s x := le_max_left _ _

theorem sum_gain_nonneg (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) :
    0 ≤ ∑ t : S i, gain G i t x :=
  Finset.sum_nonneg fun t _ => gain_nonneg G i t x

theorem one_add_sum_gain_pos (G : FiniteGame ι S) (i : ι) (x : (i : ι) → S i → ℝ) :
    0 < 1 + ∑ t : S i, gain G i t x := by
  have := sum_gain_nonneg G i x
  linarith

theorem continuous_gain (G : FiniteGame ι S) (i : ι) (s : S i) :
    Continuous fun x : (i : ι) → S i → ℝ => gain G i s x :=
  continuous_const.max ((continuous_devPayoff G i s).sub (continuous_expectedPayoff G i))

theorem continuous_nashMap (G : FiniteGame ι S) : Continuous (nashMap G) := by
  refine continuous_pi fun i => continuous_pi fun s => ?_
  have hcoord : Continuous fun x : (i : ι) → S i → ℝ => x i s := by fun_prop
  have hnum : Continuous fun x : (i : ι) → S i → ℝ => x i s + gain G i s x :=
    hcoord.add (continuous_gain G i s)
  have hden : Continuous fun x : (i : ι) → S i → ℝ => 1 + ∑ t : S i, gain G i t x :=
    continuous_const.add (continuous_finset_sum _ fun t _ => continuous_gain G i t)
  exact hnum.div hden fun x => ne_of_gt (one_add_sum_gain_pos G i x)

theorem nashMap_mapsTo (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x) :
    IsMixed (nashMap G x) := by
  intro i
  have hpos := one_add_sum_gain_pos G i x
  constructor
  · intro s
    apply div_nonneg _ hpos.le
    exact add_nonneg ((hx i).1 s) (gain_nonneg G i s x)
  · have : ∑ s : S i, nashMap G x i s
        = (∑ s : S i, (x i s + gain G i s x)) / (1 + ∑ t : S i, gain G i t x) := by
      rw [Finset.sum_div]
      rfl
    rw [this, Finset.sum_add_distrib, (hx i).2]
    exact div_self (ne_of_gt hpos)

/-- The key step: at any mixed profile some strategy in the support is not better than
the profile itself. -/
theorem exists_support_le (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ} (hx : IsMixed x)
    (i : ι) : ∃ s : S i, 0 < x i s ∧ devPayoff G i s x ≤ expectedPayoff G i x := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ s : S i, x i s * expectedPayoff G i x ≤ x i s * devPayoff G i s x := by
    intro s
    rcases lt_or_eq_of_le ((hx i).1 s) with h | h
    · exact mul_le_mul_of_nonneg_left (hcon s h).le h.le
    · rw [← h]; simp
  -- there is a strategy in the support
  obtain ⟨s0, -, hs0⟩ : ∃ s0 ∈ (Finset.univ : Finset (S i)), 0 < x i s0 := by
    by_contra h
    push_neg at h
    have : ∑ s : S i, x i s = 0 :=
      Finset.sum_eq_zero fun s hs => le_antisymm (h s hs) ((hx i).1 s)
    rw [(hx i).2] at this
    exact one_ne_zero this
  have hstrict : x i s0 * expectedPayoff G i x < x i s0 * devPayoff G i s0 x :=
    (mul_lt_mul_of_pos_left (hcon s0 hs0) hs0)
  have hsum : ∑ s : S i, x i s * expectedPayoff G i x
      < ∑ s : S i, x i s * devPayoff G i s x := by
    refine Finset.sum_lt_sum (fun s _ => ?_) ⟨s0, Finset.mem_univ _, hstrict⟩
    exact key s
  rw [← Finset.sum_mul, (hx i).2, one_mul, ← expectedPayoff_eq_sum] at hsum
  exact lt_irrefl _ hsum

/-- At a fixed point of Nash's map, no player has a profitable pure deviation. -/
theorem isNash_of_nashMap_eq (G : FiniteGame ι S) {x : (i : ι) → S i → ℝ}
    (hx : IsMixed x) (hfix : nashMap G x = x) : IsNash G x := by
  rw [isNash_iff G hx]
  intro i
  -- the total regret of player `i` vanishes
  have hpos := one_add_sum_gain_pos G i x
  obtain ⟨s0, hs0pos, hs0le⟩ := exists_support_le G hx i
  have hg0 : gain G i s0 x = 0 := by
    simp only [gain, max_eq_left_iff]
    linarith
  have hfix0 : (x i s0 + gain G i s0 x) / (1 + ∑ t : S i, gain G i t x) = x i s0 := by
    have := congrFun (congrFun hfix i) s0
    simpa [nashMap] using this
  rw [hg0, add_zero, div_eq_iff (ne_of_gt hpos)] at hfix0
  have hG : ∑ t : S i, gain G i t x = 0 := by
    have : x i s0 * (∑ t : S i, gain G i t x) = 0 := by nlinarith [hfix0]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt hs0pos)
    · exact h
  intro s
  have hzero : gain G i s x = 0 :=
    le_antisymm
      (by
        have := Finset.single_le_sum (f := fun t : S i => gain G i t x)
          (fun t _ => gain_nonneg G i t x) (Finset.mem_univ s)
        rw [hG] at this
        exact this)
      (gain_nonneg G i s x)
  have : devPayoff G i s x - expectedPayoff G i x ≤ 0 := by
    by_contra h
    push_neg at h
    rw [gain, max_eq_right h.le] at hzero
    linarith
  linarith

/-! ### The main theorem -/

/-- **Nash's theorem** (reduced to Brouwer's fixed point theorem): every finite game
in which every player has at least one strategy has a mixed strategy Nash equilibrium. -/
theorem nash_equilibrium_exists [∀ i, Nonempty (S i)]
    (hB : BrouwerProperty) (G : FiniteGame ι S) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  set K : Set ((i : ι) → S i → ℝ) := Set.univ.pi fun i => stdSimplex ℝ (S i) with hK
  have hmem : ∀ x : (i : ι) → S i → ℝ, x ∈ K ↔ IsMixed x := by
    intro x
    simp [hK, IsMixed]
  have hne : K.Nonempty := by
    refine ⟨fun i => pureVec (Classical.arbitrary (S i)), ?_⟩
    rw [hmem]
    intro i
    exact pureVec_mem_stdSimplex _
  have hcomp : IsCompact K := isCompact_univ_pi fun i => isCompact_stdSimplex (S i)
  have hconv : Convex ℝ K := convex_pi fun i _ => convex_stdSimplex ℝ (S i)
  obtain ⟨x, hxK, hfix⟩ := hB _ K hne hcomp hconv (nashMap G) (continuous_nashMap G)
    (fun y hy => (hmem _).2 (nashMap_mapsTo G ((hmem y).1 hy)))
  exact ⟨x, isNash_of_nashMap_eq G ((hmem x).1 hxK) hfix⟩

/-! ### Unconditional cases -/

/-- A pure strategy profile is a pure Nash equilibrium if no player can improve by
switching to another pure strategy. -/
def IsPureNash (G : FiniteGame ι S) (s : (i : ι) → S i) : Prop :=
  ∀ i, ∀ t : S i, G.payoff i (Function.update s i t) ≤ G.payoff i s

/-- The expected payoff at a profile of Dirac vectors is the pure payoff. -/
theorem expectedPayoff_pure (G : FiniteGame ι S) (i : ι) (σ : (i : ι) → S i) :
    expectedPayoff G i (fun j => pureVec (σ j)) = G.payoff i σ := by
  unfold expectedPayoff
  rw [Finset.sum_eq_single σ]
  · simp [pureVec]
  · intro τ _ hτ
    have : ∃ j, τ j ≠ σ j := by
      by_contra h
      push_neg at h
      exact hτ (funext h)
    obtain ⟨j, hj⟩ := this
    have : ∏ k, pureVec (σ k) (τ k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [pureVec, hj])
    rw [this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A pure Nash equilibrium gives a mixed Nash equilibrium. -/
theorem isNash_pure (G : FiniteGame ι S) {s : (i : ι) → S i} (hs : IsPureNash G s) :
    IsNash G (fun i => pureVec (s i)) := by
  have hx : IsMixed (fun i => pureVec (s i)) := fun i => pureVec_mem_stdSimplex _
  rw [isNash_iff G hx]
  intro i t
  have hup : Function.update (fun j => pureVec (s j)) i (pureVec t)
      = fun j => pureVec (Function.update s i t j) := by
    funext j
    by_cases h : j = i
    · subst h
      simp [Function.update_self]
    · simp [Function.update_of_ne h]
  rw [devPayoff, hup, expectedPayoff_pure, expectedPayoff_pure]
  exact hs i t

/-- Unconditionally (no Brouwer needed): a game with a pure Nash equilibrium has a mixed
strategy Nash equilibrium. -/
theorem nash_equilibrium_exists_of_pureNash (G : FiniteGame ι S) {s : (i : ι) → S i}
    (hs : IsPureNash G s) : ∃ x : (i : ι) → S i → ℝ, IsNash G x :=
  ⟨_, isNash_pure G hs⟩

/-- Unconditionally (no Brouwer needed): a game in which every player has a dominant
strategy has a Nash equilibrium. -/
theorem nash_equilibrium_exists_of_dominant (G : FiniteGame ι S) (s : (i : ι) → S i)
    (hdom : ∀ (i : ι) (σ : (i : ι) → S i) (t : S i),
      G.payoff i (Function.update σ i t) ≤ G.payoff i (Function.update σ i (s i))) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  refine nash_equilibrium_exists_of_pureNash G (s := s) fun i t => ?_
  have h := hdom i s t
  rwa [Function.update_eq_self] at h

/-- Unconditionally (no Brouwer needed): a finite *potential* game has a Nash
equilibrium; indeed a maximizer of the potential is a pure Nash equilibrium. -/
theorem nash_equilibrium_exists_of_potential [∀ i, Nonempty (S i)]
    (G : FiniteGame ι S) (P : ((i : ι) → S i) → ℝ)
    (hP : ∀ (i : ι) (s : (i : ι) → S i) (t : S i),
      G.payoff i (Function.update s i t) - G.payoff i s
        = P (Function.update s i t) - P s) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  obtain ⟨s, hmax⟩ := Finite.exists_max (fun σ : (i : ι) → S i => P σ)
  refine ⟨fun i => pureVec (s i), isNash_pure G ?_⟩
  intro i t
  have h1 := hP i s t
  have h2 := hmax (Function.update s i t)
  linarith

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

