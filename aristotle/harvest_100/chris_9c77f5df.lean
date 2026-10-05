import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

/-! ## Part 1: elementary finite information theory -/

/-- Kullback–Leibler divergence of `p` from `q`, over a finite alphabet.
With the `Real.log` conventions, terms with `p i = 0` contribute `0`. -/
noncomputable def KL {γ : Type*} [Fintype γ] (p q : γ → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- Gibbs' inequality: the KL divergence between two probability vectors is nonnegative
(assuming absolute continuity of `p` with respect to `q`). -/
theorem KL_nonneg {γ : Type*} [Fintype γ] (p q : γ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hac : ∀ i, p i ≠ 0 → q i ≠ 0) : 0 ≤ KL p q := by
  have key : ∀ i, -(p i * Real.log (p i / q i)) ≤ q i - p i := by
    intro i
    rcases eq_or_lt_of_le (hp i) with h0 | h0
    · simp [← h0, hq i]
    · have hqi : 0 < q i := lt_of_le_of_ne (hq i) (fun hh => hac i (ne_of_gt h0) hh.symm)
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hmul : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt h0)] at hmul
      calc -(p i * Real.log (p i / q i)) = p i * Real.log (q i / p i) := by
            rw [Real.log_div (ne_of_gt h0) (ne_of_gt hqi),
              Real.log_div (ne_of_gt hqi) (ne_of_gt h0)]
            ring
        _ ≤ q i - p i * 1 := hmul
        _ = q i - p i := by ring
  have hsum : ∑ i, -(p i * Real.log (p i / q i)) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum (fun i _ => key i)
  rw [Finset.sum_sub_distrib, hps, hqs] at hsum
  simp only [Finset.sum_neg_distrib, KL] at hsum ⊢
  linarith

/-- Mutual information of a joint probability distribution `p` on a product of finite sets:
the KL divergence of the joint from the product of its marginals. -/
noncomputable def MI {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * Real.log (p x y / ((∑ y', p x y') * (∑ x', p x' y)))

/-- Mutual information of a probability distribution is nonnegative. -/
theorem MI_nonneg {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ)
    (hp : ∀ x y, 0 ≤ p x y) (hs : ∑ x, ∑ y, p x y = 1) : 0 ≤ MI p := by
  set P : α × β → ℝ := fun z => p z.1 z.2 with hP
  set Q : α × β → ℝ := fun z => (∑ y', p z.1 y') * (∑ x', p x' z.2) with hQ
  have hm1 : ∑ x, (∑ y', p x y') = 1 := hs
  have hm2 : ∑ y, (∑ x', p x' y) = 1 := by rw [Finset.sum_comm]; exact hs
  have hKL := KL_nonneg P Q (fun _ => hp _ _)
    (fun _ => mul_nonneg (Finset.sum_nonneg fun _ _ => hp _ _)
      (Finset.sum_nonneg fun _ _ => hp _ _))
    (by rw [Fintype.sum_prod_type]; exact hs)
    (by
      rw [Fintype.sum_prod_type]
      simp only [hQ, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hm2]
      simpa using hm1)
    (by
      rintro ⟨x, y⟩ hne
      have hpos : 0 < p x y := lt_of_le_of_ne (hp x y) (Ne.symm hne)
      have h1 : 0 < ∑ y', p x y' :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun y' => p x y')
          (fun _ _ => hp _ _) (Finset.mem_univ y))
      have h2 : 0 < ∑ x', p x' y :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun x' => p x' y)
          (fun _ _ => hp _ _) (Finset.mem_univ x))
      exact ne_of_gt (mul_pos h1 h2))
  rw [KL, Fintype.sum_prod_type] at hKL
  exact hKL

/-- A joint distribution that factorises as a product of two probability distributions
has zero mutual information. -/
theorem MI_eq_zero_of_indep {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ)
    (g : α → ℝ) (h : β → ℝ) (hfac : ∀ x y, p x y = g x * h y)
    (hg : ∑ x, g x = 1) (hh : ∑ y, h y = 1) : MI p = 0 := by
  have hm1 : ∀ x, (∑ y', p x y') = g x := by
    intro x; simp only [hfac, ← Finset.mul_sum, hh, mul_one]
  have hm2 : ∀ y, (∑ x', p x' y) = h y := by
    intro y; simp only [hfac, ← Finset.sum_mul, hg, one_mul]
  simp only [MI, hm1, hm2, ← hfac]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  rcases eq_or_ne (p x y) 0 with h0 | h0
  · simp [h0]
  · rw [div_self h0]; simp

/-! ## Part 2: discrete dynamical systems with a connectivity structure -/

/-- A finite system of binary nodes with stochastic, local dynamics.

* `E u v` means "node `v` receives input from node `u`";
* `f v s b` is the probability that node `v` is in state `b` at the next time step,
  given that the whole system is in state `s` now;
* `f_local` says the dynamics of `v` depends only on the states of its input nodes.
The nodes update independently given the current state, so the transition probability
of the whole system is the product of the `f v`. -/
structure System (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Connectivity: `E u v` means node `v` receives input from node `u`. -/
  E : V → V → Prop
  /-- `f v s b` is the probability that node `v` takes value `b` next, given current state `s`. -/
  f : V → (V → Bool) → Bool → ℝ
  /-- Probabilities are nonnegative. -/
  f_nonneg : ∀ v s b, 0 ≤ f v s b
  /-- Probabilities of the two possible next values of a node sum to one. -/
  f_sum : ∀ v s, f v s true + f v s false = 1
  /-- The dynamics of a node only depends on the current state of its input nodes. -/
  f_local : ∀ v s s', (∀ u, E u v → s u = s' u) → f v s = f v s'

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Combine a state of the part `A` and a state of its complement into a global state. -/
def comb (A : Finset V) (a : {v // v ∈ A} → Bool) (b : {v // v ∉ A} → Bool) : V → Bool :=
  fun v => if h : v ∈ A then a ⟨v, h⟩ else b ⟨v, h⟩

omit [Fintype V] in
@[simp] lemma comb_mem (A : Finset V) (a : {v // v ∈ A} → Bool) (b : {v // v ∉ A} → Bool)
    (v : V) (h : v ∈ A) : comb A a b v = a ⟨v, h⟩ := by
  simp [comb, h]

omit [Fintype V] in
@[simp] lemma comb_not_mem (A : Finset V) (a : {v // v ∈ A} → Bool) (b : {v // v ∉ A} → Bool)
    (v : V) (h : v ∉ A) : comb A a b v = b ⟨v, h⟩ := by
  simp [comb, h]

/-- Summing over states of a part and of its complement is summing over global states. -/
lemma sum_comb (A : Finset V) (F : (V → Bool) → ℝ) :
    ∑ a : {v // v ∈ A} → Bool, ∑ b : {v // v ∉ A} → Bool, F (comb A a b)
      = ∑ s : V → Bool, F s := by
  have H : ∑ z : ({v // v ∈ A} → Bool) × ({v // v ∉ A} → Bool), F (comb A z.1 z.2)
      = ∑ s : V → Bool, F s :=
    Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ => Bool)).symm _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type] at H
  exact H

/-- The transition probabilities of independently updating binary nodes sum to one. -/
lemma sum_prod_node {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → Bool → ℝ)
    (h : ∀ v, g v true + g v false = 1) : ∑ t : ι → Bool, ∏ v, g v (t v) = 1 := by
  have H := Finset.prod_univ_sum (κ := fun _ : ι => Bool) (fun _ => Finset.univ) g
  rw [Fintype.piFinset_univ] at H
  rw [← H]
  simp [h]

/-- The probability that the system moves from state `s` to state `t` in one step. -/
noncomputable def transProb (S : System V) (s t : V → Bool) : ℝ := ∏ v, S.f v s (t v)

/-- The joint distribution of (present state, next state) when the present state
is drawn uniformly at random (the maximum-entropy "unconstrained" input). -/
noncomputable def joint (S : System V) (s t : V → Bool) : ℝ :=
  ((2 : ℝ) ^ Fintype.card V)⁻¹ * transProb S s t

lemma joint_nonneg (S : System V) (s t : V → Bool) : 0 ≤ joint S s t := by
  refine mul_nonneg (by positivity) ?_
  exact Finset.prod_nonneg fun v _ => S.f_nonneg _ _ _

lemma sum_transProb (S : System V) (s : V → Bool) : ∑ t : V → Bool, transProb S s t = 1 :=
  sum_prod_node (fun v b => S.f v s b) (fun v => S.f_sum v s)

lemma sum_joint (S : System V) : ∑ s : V → Bool, ∑ t : V → Bool, joint S s t = 1 := by
  have h1 : ∀ s : V → Bool, ∑ t : V → Bool, joint S s t = ((2 : ℝ) ^ Fintype.card V)⁻¹ := by
    intro s
    simp only [joint, ← Finset.mul_sum, sum_transProb, mul_one]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_bool]
  have : ((2 : ℕ) : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  push_cast
  field_simp

/-- The joint distribution of the trajectories (present, next) of the part `A` and of its
complement, when the present global state is uniform. -/
noncomputable def partJoint (S : System V) (A : Finset V)
    (x : (({v // v ∈ A} → Bool) × ({v // v ∈ A} → Bool)))
    (y : (({v // v ∉ A} → Bool) × ({v // v ∉ A} → Bool))) : ℝ :=
  joint S (comb A x.1 y.1) (comb A x.2 y.2)

/-- Effective information across the bipartition `{A, Aᶜ}`: the mutual information between
the trajectory (present and next state) of the part `A` and the trajectory of its complement,
with the present global state drawn uniformly. It vanishes exactly when the two parts of the
system evolve independently of one another. -/
noncomputable def EI (S : System V) (A : Finset V) : ℝ := MI (partJoint S A)

/-- Integrated information `Φ`: the minimum of the effective information over all
bipartitions of the system into two nonempty parts. -/
noncomputable def Phi (S : System V) : ℝ :=
  sInf {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI S A}

lemma partJoint_nonneg (S : System V) (A : Finset V) (x y) : 0 ≤ partJoint S A x y :=
  joint_nonneg _ _ _

lemma sum_partJoint (S : System V) (A : Finset V) :
    ∑ x, ∑ y, partJoint S A x y = 1 := by
  have step : ∀ x1 : {v // v ∈ A} → Bool, ∀ y1 : {v // v ∉ A} → Bool,
      ∑ x2 : {v // v ∈ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
        joint S (comb A x1 y1) (comb A x2 y2)
        = ∑ t : V → Bool, joint S (comb A x1 y1) t := by
    intro x1 y1
    exact sum_comb A (fun t => joint S (comb A x1 y1) t)
  calc ∑ x, ∑ y, partJoint S A x y
      = ∑ x1 : {v // v ∈ A} → Bool, ∑ x2 : {v // v ∈ A} → Bool,
          ∑ y1 : {v // v ∉ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
            joint S (comb A x1 y1) (comb A x2 y2) := by
        simp only [partJoint, Fintype.sum_prod_type]
    _ = ∑ x1 : {v // v ∈ A} → Bool, ∑ y1 : {v // v ∉ A} → Bool,
          ∑ x2 : {v // v ∈ A} → Bool, ∑ y2 : {v // v ∉ A} → Bool,
            joint S (comb A x1 y1) (comb A x2 y2) := by
        exact Finset.sum_congr rfl fun x1 _ => Finset.sum_comm
    _ = ∑ x1 : {v // v ∈ A} → Bool, ∑ y1 : {v // v ∉ A} → Bool,
          ∑ t : V → Bool, joint S (comb A x1 y1) t := by
        exact Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun y1 _ => step x1 y1
    _ = ∑ s : V → Bool, ∑ t : V → Bool, joint S s t :=
        sum_comb A (fun s => ∑ t : V → Bool, joint S s t)
    _ = 1 := sum_joint S

/-- Effective information across any bipartition is nonnegative. -/
theorem EI_nonneg (S : System V) (A : Finset V) : 0 ≤ EI S A :=
  MI_nonneg _ (partJoint_nonneg S A) (sum_partJoint S A)

lemma card_part_add (A : Finset V) :
    Fintype.card {v // v ∈ A} + Fintype.card {v // v ∉ A} = Fintype.card V := by
  have h1 : A.card ≤ Fintype.card V := by simpa using Finset.card_le_univ A
  simp [Fintype.card_subtype_compl, Fintype.card_coe]
  omega

/-- Splitting a product over the nodes into the part `A` and its complement. -/
lemma prod_split (A : Finset V) (F : V → ℝ) :
    (∏ v : {v // v ∈ A}, F v) * (∏ v : {v // v ∉ A}, F v) = ∏ v, F v := by
  have h1 : (∏ v : {v // v ∈ A}, F v) = ∏ v ∈ A, F v := Finset.prod_coe_sort A F
  have h2 : (∏ v : {v // v ∉ A}, F v) = ∏ v ∈ Aᶜ, F v := by
    rw [← Finset.prod_coe_sort Aᶜ F]
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight (by simp)) _ _ (fun _ => rfl)
  rw [h1, h2, Finset.prod_mul_prod_compl]

/-- If no connection of the system crosses the bipartition `{A, Aᶜ}`, then the effective
information across that bipartition vanishes. -/
theorem EI_eq_zero_of_cut (S : System V) (A : Finset V)
    (hcut : ∀ u v, S.E u v → (u ∈ A ↔ v ∈ A)) : EI S A = 0 := by
  set r1 : {v // v ∈ A} → Bool := fun _ => false with hr1
  set r2 : {v // v ∉ A} → Bool := fun _ => false with hr2
  set wA : ℝ := ((2 : ℝ) ^ Fintype.card {v // v ∈ A})⁻¹ with hwA
  set wB : ℝ := ((2 : ℝ) ^ Fintype.card {v // v ∉ A})⁻¹ with hwB
  set g : (({v // v ∈ A} → Bool) × ({v // v ∈ A} → Bool)) → ℝ :=
    fun x => wA * ∏ v : {v // v ∈ A}, S.f v (comb A x.1 r2) (x.2 v) with hg
  set h : (({v // v ∉ A} → Bool) × ({v // v ∉ A} → Bool)) → ℝ :=
    fun y => wB * ∏ v : {v // v ∉ A}, S.f v (comb A r1 y.1) (y.2 v) with hh
  refine MI_eq_zero_of_indep _ g h ?_ ?_ ?_
  · -- factorisation
    intro x y
    have hw : ((2 : ℝ) ^ Fintype.card V)⁻¹ = wA * wB := by
      rw [hwA, hwB, ← mul_inv, ← pow_add, card_part_add]
    have hA' : ∀ v : {v // v ∈ A},
        S.f v (comb A x.1 y.1) (comb A x.2 y.2 v) = S.f v (comb A x.1 r2) (x.2 v) := by
      rintro ⟨v, hv⟩
      have h1 : S.f v (comb A x.1 y.1) = S.f v (comb A x.1 r2) := by
        refine S.f_local v _ _ ?_
        intro u hu
        have : u ∈ A := (hcut u v hu).mpr hv
        simp [comb, this]
      rw [h1]
      simp [comb, hv]
    have hB' : ∀ v : {v // v ∉ A},
        S.f v (comb A x.1 y.1) (comb A x.2 y.2 v) = S.f v (comb A r1 y.1) (y.2 v) := by
      rintro ⟨v, hv⟩
      have h1 : S.f v (comb A x.1 y.1) = S.f v (comb A r1 y.1) := by
        refine S.f_local v _ _ ?_
        intro u hu
        have : u ∉ A := fun hu' => hv ((hcut u v hu).mp hu')
        simp [comb, this]
      rw [h1]
      simp [comb, hv]
    simp only [partJoint, joint, transProb, hg, hh]
    rw [← prod_split A (fun v => S.f v (comb A x.1 y.1) (comb A x.2 y.2 v)), hw]
    rw [Finset.prod_congr rfl (fun v _ => hA' v), Finset.prod_congr rfl (fun v _ => hB' v)]
    ring
  · -- `g` is a probability distribution
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x1 : {v // v ∈ A} → Bool,
        ∑ x2 : {v // v ∈ A} → Bool, g (x1, x2) = wA := by
      intro x1
      simp only [hg, ← Finset.mul_sum]
      have hone : (∑ t : {v // v ∈ A} → Bool, ∏ v : {v // v ∈ A},
          S.f v (comb A x1 r2) (t v)) = 1 :=
        sum_prod_node (ι := {v // v ∈ A}) (fun v b => S.f v (comb A x1 r2) b)
          (fun v => S.f_sum v (comb A x1 r2))
      rw [hone, mul_one]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_bool, hwA]
    have : ((2 : ℕ) : ℝ) ^ Fintype.card {v // v ∈ A} ≠ 0 := by positivity
    push_cast
    field_simp
  · -- `h` is a probability distribution
    rw [Fintype.sum_prod_type]
    have hinner : ∀ y1 : {v // v ∉ A} → Bool,
        ∑ y2 : {v // v ∉ A} → Bool, h (y1, y2) = wB := by
      intro y1
      simp only [hh, ← Finset.mul_sum]
      have hone : (∑ t : {v // v ∉ A} → Bool, ∏ v : {v // v ∉ A},
          S.f v (comb A r1 y1) (t v)) = 1 :=
        sum_prod_node (ι := {v // v ∉ A}) (fun v b => S.f v (comb A r1 y1) b)
          (fun v => S.f_sum v (comb A r1 y1))
      rw [hone, mul_one]
    simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
      Fintype.card_bool, hwB]
    have : ((2 : ℕ) : ℝ) ^ Fintype.card {v // v ∉ A} ≠ 0 := by positivity
    push_cast
    field_simp

/-- **Integrated information vanishes for a disconnected system.**

If the connectivity of the system admits a bipartition into two nonempty parts `A` and `Aᶜ`
with no connection crossing between them, then the integrated information `Φ`, defined as the
minimum over bipartitions of the effective information across the bipartition, is zero. -/
theorem iit_phi_partition (S : System V) (A : Finset V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hcut : ∀ u v, S.E u v → (u ∈ A ↔ v ∈ A)) :
    Phi S = 0 := by
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI S A} :=
    ⟨A, hA, hAc, (EI_eq_zero_of_cut S A hcut).symm⟩
  have hbdd : BddBelow {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI S A} := by
    refine ⟨0, ?_⟩
    rintro r ⟨B, -, -, rfl⟩
    exact EI_nonneg S B
  refine le_antisymm (csInf_le hbdd hmem) ?_
  refine le_csInf ⟨0, hmem⟩ ?_
  rintro r ⟨B, -, -, rfl⟩
  exact EI_nonneg S B

/-! ## Part 3: the definitions are not vacuous -/

/-- A system of independent fair coins: no node influences any other. -/
noncomputable def coinSystem (V : Type*) [Fintype V] [DecidableEq V] : System V where
  E := fun _ _ => False
  f := fun _ _ _ => 1 / 2
  f_nonneg := by norm_num
  f_sum := by norm_num
  f_local := by intro v s s' _; rfl

/-- The two-node system of independent coins is disconnected, hence has `Φ = 0`. -/
example : Phi (coinSystem Bool) = 0 := by
  refine iit_phi_partition _ {true} ⟨true, by decide⟩ ⟨false, by decide⟩ ?_
  intro u v hE
  exact absurd hE (by simp [coinSystem])

end Frontier

