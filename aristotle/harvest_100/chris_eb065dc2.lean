/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/
def restr (A : Finset V) (x : V → Bool) : ↥A → Bool := fun i => x i.1

/-- Recombining a state of the part `A` and a state of its complement into a global state. -/
def joinState (A : Finset V) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) : V → Bool :=
  fun i => if h : i ∈ A then u ⟨i, h⟩ else v ⟨i, Finset.mem_compl.mpr h⟩

@[simp] lemma restr_joinState_self (A : Finset V) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr A (joinState A u v) = u := by
  funext i
  simp [restr, joinState, i.2]

@[simp] lemma restr_compl_joinState (A : Finset V) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr Aᶜ (joinState A u v) = v := by
  funext i
  have hi : (i : V) ∉ A := Finset.mem_compl.mp i.2
  simp [restr, joinState, hi]

/-- Splitting a global state into the pair of its restrictions to `A` and to `Aᶜ`. -/
def splitEquiv (A : Finset V) : ((↥A → Bool) × (↥Aᶜ → Bool)) ≃ (V → Bool) where
  toFun uv := joinState A uv.1 uv.2
  invFun x := (restr A x, restr Aᶜ x)
  left_inv uv := by ext <;> simp
  right_inv x := by
    funext i
    by_cases h : i ∈ A <;> simp [joinState, restr, h]

/-- The probability, under a uniform ("maximum-entropy") perturbation of the current state,
that the next state of the system restricted to `A` is `a` and restricted to `Aᶜ` is `b`.
This is the *effect repertoire* of the deterministic transition function `f`. -/
noncomputable def jointProb (f : (V → Bool) → (V → Bool)) (A : Finset V)
    (a : ↥A → Bool) (b : ↥Aᶜ → Bool) : ℝ :=
  (∑ x : V → Bool, if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) /
    (Fintype.card (V → Bool) : ℝ)

/-- The marginal effect repertoire of the part `A`. -/
noncomputable def margA (f : (V → Bool) → (V → Bool)) (A : Finset V) (a : ↥A → Bool) : ℝ :=
  ∑ b : ↥Aᶜ → Bool, jointProb f A a b

/-- The marginal effect repertoire of the part `Aᶜ`. -/
noncomputable def margB (f : (V → Bool) → (V → Bool)) (A : Finset V) (b : ↥Aᶜ → Bool) : ℝ :=
  ∑ a : ↥A → Bool, jointProb f A a b

/-- The **effective information** across the bipartition `(A, Aᶜ)`: the Kullback-Leibler
divergence between the effect repertoire of the whole system and the product of the effect
repertoires of the two parts (i.e. the effect repertoire of the system whose connections
across the cut have been severed and replaced by independent noise). -/
noncomputable def EI (f : (V → Bool) → (V → Bool)) (A : Finset V) : ℝ :=
  ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
    jointProb f A a b * Real.log (jointProb f A a b / (margA f A a * margB f A b))

/-- **Integrated information** `Φ`: the effective information minimized over all
nontrivial bipartitions of the system. -/
noncomputable def Phi (f : (V → Bool) → (V → Bool)) : ℝ :=
  sInf {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI f A}

/-- The system `f` is *disconnected along the cut `A`* when the next state of the nodes in `A`
depends only on the current state of `A`, and the next state of the nodes outside `A` depends
only on the current state outside `A`: there are no causal connections across the cut. -/
def DisconnectedAt (f : (V → Bool) → (V → Bool)) (A : Finset V) : Prop :=
  (∀ x y : V → Bool, (∀ i ∈ A, x i = y i) → ∀ i ∈ A, f x i = f y i) ∧
  (∀ x y : V → Bool, (∀ i ∉ A, x i = y i) → ∀ i ∉ A, f x i = f y i)

section Lemmas

variable (f : (V → Bool) → (V → Bool)) (A : Finset V)

lemma card_pos_real : (0 : ℝ) < (Fintype.card (V → Bool) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma jointProb_nonneg (a : ↥A → Bool) (b : ↥Aᶜ → Bool) : 0 ≤ jointProb f A a b := by
  apply div_nonneg _ (le_of_lt (card_pos_real (V := V)))
  exact Finset.sum_nonneg fun x _ => by positivity

lemma jointProb_total : ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool, jointProb f A a b = 1 := by
  have hN : (Fintype.card (V → Bool) : ℝ) ≠ 0 := ne_of_gt (card_pos_real (V := V))
  have hpt : ∀ x : V → Bool, ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
      (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) = 1 := by
    intro x
    simp [ite_and]
  simp only [jointProb, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hN]
  calc (∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool, ∑ x : V → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0))
      = ∑ a : ↥A → Bool, ∑ x : V → Bool, ∑ b : ↥Aᶜ → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x : V → Bool, ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
          (if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ _x : V → Bool, (1 : ℝ) := Finset.sum_congr rfl fun x _ => hpt x
    _ = (Fintype.card (V → Bool) : ℝ) := by simp

lemma margA_nonneg (a : ↥A → Bool) : 0 ≤ margA f A a :=
  Finset.sum_nonneg fun b _ => jointProb_nonneg f A a b

lemma margB_nonneg (b : ↥Aᶜ → Bool) : 0 ≤ margB f A b :=
  Finset.sum_nonneg fun a _ => jointProb_nonneg f A a b

lemma jointProb_le_margA (a : ↥A → Bool) (b : ↥Aᶜ → Bool) : jointProb f A a b ≤ margA f A a :=
  Finset.single_le_sum (f := fun b => jointProb f A a b)
    (fun b _ => jointProb_nonneg f A a b) (Finset.mem_univ b)

lemma jointProb_le_margB (a : ↥A → Bool) (b : ↥Aᶜ → Bool) : jointProb f A a b ≤ margB f A b :=
  Finset.single_le_sum (f := fun a => jointProb f A a b)
    (fun a _ => jointProb_nonneg f A a b) (Finset.mem_univ a)

lemma margA_total : ∑ a : ↥A → Bool, margA f A a = 1 := jointProb_total f A

lemma margB_total : ∑ b : ↥Aᶜ → Bool, margB f A b = 1 := by
  rw [← jointProb_total f A]
  exact Finset.sum_comm

/-- Gibbs' inequality, term by term: `p * log (p / q) ≥ p - q`. -/
lemma term_lower_bound {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  rcases eq_or_lt_of_le hp with h | h
  · simp [← h]
    linarith
  · have hq' : 0 < q := hpq h
    have hlog : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hinv : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have h1 : 1 - q / p ≤ Real.log (p / q) := by rw [hinv]; linarith
    have h2 : p * (1 - q / p) ≤ p * Real.log (p / q) := by nlinarith
    have h3 : p * (1 - q / p) = p - q := by field_simp
    linarith

lemma EI_nonneg : 0 ≤ EI f A := by
  have hsum : ∑ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
      (jointProb f A a b - margA f A a * margB f A b) = 0 := by
    have hrow : ∀ a : ↥A → Bool, ∑ b : ↥Aᶜ → Bool,
        (jointProb f A a b - margA f A a * margB f A b) = 0 := by
      intro a
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, margB_total f A, mul_one]
      simp [margA]
    simp [hrow]
  rw [← hsum, EI]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  refine term_lower_bound (jointProb_nonneg f A a b)
    (mul_nonneg (margA_nonneg f A a) (margB_nonneg f A b)) ?_
  intro hpos
  exact mul_pos (lt_of_lt_of_le hpos (jointProb_le_margA f A a b))
    (lt_of_lt_of_le hpos (jointProb_le_margB f A a b))

/-- Effective information vanishes when the effect repertoire factorizes across the cut. -/
lemma EI_eq_zero_of_factorizes
    (h : ∀ a b, jointProb f A a b = margA f A a * margB f A b) : EI f A = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [h a b]
  rcases eq_or_ne (margA f A a * margB f A b) 0 with h0 | h0
  · rw [h0]; simp
  · rw [div_self h0, Real.log_one, mul_zero]

end Lemmas

section Disconnected

variable (f : (V → Bool) → (V → Bool)) (A : Finset V)

lemma sum_split (g : (V → Bool) → ℝ) :
    ∑ x : V → Bool, g x =
      ∑ u : ↥A → Bool, ∑ v : ↥Aᶜ → Bool, g (joinState A u v) := by
  rw [← Equiv.sum_comp (splitEquiv A) g]
  exact Fintype.sum_prod_type _

/-- The number of `A`-states leading to `a`. -/
noncomputable def cntA (f : (V → Bool) → (V → Bool)) (A : Finset V) (a : ↥A → Bool) : ℝ :=
  ∑ u : ↥A → Bool, if restr A (f (joinState A u (fun _ => false))) = a then (1 : ℝ) else 0

/-- The number of `Aᶜ`-states leading to `b`. -/
noncomputable def cntB (f : (V → Bool) → (V → Bool)) (A : Finset V) (b : ↥Aᶜ → Bool) : ℝ :=
  ∑ v : ↥Aᶜ → Bool, if restr Aᶜ (f (joinState A (fun _ => false) v)) = b then (1 : ℝ) else 0

lemma cntA_total : ∑ a : ↥A → Bool, cntA f A a = (Fintype.card (↥A → Bool) : ℝ) := by
  unfold cntA
  rw [Finset.sum_comm]
  simp

lemma cntB_total : ∑ b : ↥Aᶜ → Bool, cntB f A b = (Fintype.card (↥Aᶜ → Bool) : ℝ) := by
  unfold cntB
  rw [Finset.sum_comm]
  simp

lemma card_split : (Fintype.card (V → Bool) : ℝ)
    = (Fintype.card (↥A → Bool) : ℝ) * (Fintype.card (↥Aᶜ → Bool) : ℝ) := by
  have hc := Fintype.card_congr (splitEquiv A)
  rw [Fintype.card_prod] at hc
  rw [← hc]
  push_cast
  ring

/-- Across a disconnected cut, the next state of `A` is determined by the current state of `A`. -/
lemma restrA_indep (h : DisconnectedAt f A) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr A (f (joinState A u v)) = restr A (f (joinState A u (fun _ => false))) := by
  funext i
  simp only [restr]
  exact h.1 _ _ (fun j hj => by simp [joinState, hj]) i i.2

/-- Across a disconnected cut, the next state of `Aᶜ` is determined by the current state of
`Aᶜ`. -/
lemma restrB_indep (h : DisconnectedAt f A) (u : ↥A → Bool) (v : ↥Aᶜ → Bool) :
    restr Aᶜ (f (joinState A u v)) = restr Aᶜ (f (joinState A (fun _ => false) v)) := by
  funext i
  have hi : (i : V) ∉ A := Finset.mem_compl.mp i.2
  simp only [restr]
  exact h.2 _ _ (fun j hj => by simp [joinState, hj]) i hi

lemma num_factor (h : DisconnectedAt f A) (a : ↥A → Bool) (b : ↥Aᶜ → Bool) :
    (∑ x : V → Bool, if restr A (f x) = a ∧ restr Aᶜ (f x) = b then (1 : ℝ) else 0)
      = cntA f A a * cntB f A b := by
  rw [sum_split A, cntA, cntB, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [restrA_indep f A h u v, restrB_indep f A h u v]
  by_cases h1 : restr A (f (joinState A u (fun _ => false))) = a <;>
    by_cases h2 : restr Aᶜ (f (joinState A (fun _ => false) v)) = b <;> simp [h1, h2]

lemma margA_eq (h : DisconnectedAt f A) (a : ↥A → Bool) :
    margA f A a = cntA f A a / (Fintype.card (↥A → Bool) : ℝ) := by
  have hNA : (Fintype.card (↥A → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNB : (Fintype.card (↥Aᶜ → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold margA
  simp only [jointProb, num_factor f A h]
  rw [← Finset.sum_div, ← Finset.mul_sum, cntB_total, card_split A]
  field_simp

lemma margB_eq (h : DisconnectedAt f A) (b : ↥Aᶜ → Bool) :
    margB f A b = cntB f A b / (Fintype.card (↥Aᶜ → Bool) : ℝ) := by
  have hNA : (Fintype.card (↥A → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNB : (Fintype.card (↥Aᶜ → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold margB
  simp only [jointProb, num_factor f A h]
  rw [← Finset.sum_div, ← Finset.sum_mul, cntA_total, card_split A]
  field_simp

lemma jointProb_factorizes (h : DisconnectedAt f A) (a : ↥A → Bool) (b : ↥Aᶜ → Bool) :
    jointProb f A a b = margA f A a * margB f A b := by
  rw [margA_eq f A h a, margB_eq f A h b, jointProb, num_factor f A h, card_split A,
    div_mul_div_comm]

lemma EI_eq_zero_of_disconnected (h : DisconnectedAt f A) : EI f A = 0 :=
  EI_eq_zero_of_factorizes f A (jointProb_factorizes f A h)

end Disconnected

/-- **Integrated information of a disconnected system vanishes.**

Model: a finite system of `V` binary nodes with deterministic transition function
`f : (V → Bool) → (V → Bool)`.  Perturbing the system into a uniformly random current state
(the maximum-entropy / "do"-intervention of IIT), the effect repertoire `jointProb` is the
distribution of the next state, described through a bipartition `(A, Aᶜ)`.  The effective
information `EI f A` across that cut is the Kullback-Leibler divergence between the effect
repertoire and the product of the two marginal (cut) repertoires, and integrated information
`Φ` is the minimum of `EI` over all nontrivial bipartitions.

If the system is disconnected, i.e. there is a nontrivial bipartition `(A, Aᶜ)` across which no
node influences the other side, then `Φ f = 0`. -/
theorem iit_phi_partition (f : (V → Bool) → (V → Bool)) (A : Finset V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) (hdisc : DisconnectedAt f A) :
    Phi f = 0 := by
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI f A} :=
    ⟨A, hA, hAc, (EI_eq_zero_of_disconnected f A hdisc).symm⟩
  have hlb : ∀ r ∈ {r : ℝ | ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧ r = EI f A}, (0 : ℝ) ≤ r := by
    rintro r ⟨B, -, -, rfl⟩
    exact EI_nonneg f B
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, fun r hr => hlb r hr⟩ hmem
  · exact le_csInf ⟨0, hmem⟩ hlb

/-! ### Non-degeneracy: a connected system with strictly positive effective information

The definitions above are not vacuous: for the two-node system in which both nodes copy the
state of the first node, the effective information across the (unique) bipartition equals
`log 2 > 0`. -/

section Nondegenerate

/-- The two-node system in which both nodes copy the state of node `0`. -/
def copySys : (Fin 2 → Bool) → (Fin 2 → Bool) := fun x _ => x 0

/-- The bipartition of the two-node system into `{0}` and `{1}`. -/
def leftPart : Finset (Fin 2) := {0}

instance : Unique (↥leftPart) where
  default := ⟨0, by decide⟩
  uniq i := Subtype.ext (Finset.mem_singleton.mp i.2)

instance : Unique (↥leftPartᶜ) where
  default := ⟨1, by decide⟩
  uniq i := by
    have h : (i : Fin 2) ∉ leftPart := Finset.mem_compl.mp i.2
    have h' : (i : Fin 2) ≠ 0 := fun hc => h (by simp [leftPart, hc])
    have h2 : ∀ j : Fin 2, j ≠ 0 → j = 1 := by decide
    exact Subtype.ext (h2 _ h')

lemma sum_funUnique {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι] (g : (ι → Bool) → ℝ) :
    ∑ h : ι → Bool, g h = g (fun _ => true) + g (fun _ => false) := by
  rw [← Equiv.sum_comp (Equiv.funUnique ι Bool).symm g, Fintype.sum_bool]
  rfl

lemma sum_left (g : (↥leftPart → Bool) → ℝ) :
    ∑ a : ↥leftPart → Bool, g a = g (fun _ => true) + g (fun _ => false) := sum_funUnique g

lemma sum_right (g : (↥leftPartᶜ → Bool) → ℝ) :
    ∑ b : ↥leftPartᶜ → Bool, g b = g (fun _ => true) + g (fun _ => false) := sum_funUnique g

lemma sum_fin2_first (F : Bool → ℝ) :
    ∑ x : Fin 2 → Bool, F (x 0) = 2 * F true + 2 * F false := by
  rw [← Equiv.sum_comp (piFinTwoEquiv (fun _ => Bool)).symm (fun x => F (x 0))]
  simp [Fintype.sum_prod_type]

lemma const_eq_iff {ι : Type*} [Unique ι] (c : Bool) (a : ι → Bool) :
    ((fun _ : ι => c) = a) ↔ c = a default := by
  constructor
  · intro h; rw [← h]
  · intro h; funext i; rw [Unique.eq_default i]; exact h

lemma jointProb_copySys (a : ↥leftPart → Bool) (b : ↥leftPartᶜ → Bool) :
    jointProb copySys leftPart a b = if a default = b default then 1 / 2 else 0 := by
  have hcard : (Fintype.card (Fin 2 → Bool) : ℝ) = 4 := by simp
  have hnum : (∑ x : Fin 2 → Bool,
      if restr leftPart (copySys x) = a ∧ restr leftPartᶜ (copySys x) = b then (1 : ℝ) else 0)
      = if a default = b default then 2 else 0 := by
    have hpt : ∀ x : Fin 2 → Bool,
        (if restr leftPart (copySys x) = a ∧ restr leftPartᶜ (copySys x) = b then (1 : ℝ) else 0)
          = (fun c : Bool => if c = a default ∧ c = b default then (1 : ℝ) else 0) (x 0) := by
      intro x
      have h1 : (restr leftPart (copySys x) = a) ↔ x 0 = a default := const_eq_iff (x 0) a
      have h2 : (restr leftPartᶜ (copySys x) = b) ↔ x 0 = b default := const_eq_iff (x 0) b
      simp only [h1, h2]
    refine (Finset.sum_congr rfl fun x _ => hpt x).trans
      ((sum_fin2_first fun c : Bool => if c = a default ∧ c = b default then (1 : ℝ) else 0).trans
        ?_)
    cases hA : a default <;> cases hB : b default <;> norm_num
  rw [jointProb, hnum, hcard]
  by_cases h : a default = b default <;> norm_num [h]

lemma margA_copySys (a : ↥leftPart → Bool) : margA copySys leftPart a = 1 / 2 := by
  rw [margA, sum_right (fun b => jointProb copySys leftPart a b)]
  simp only [jointProb_copySys]
  cases hA : a default <;> norm_num

lemma margB_copySys (b : ↥leftPartᶜ → Bool) : margB copySys leftPart b = 1 / 2 := by
  rw [margB, sum_left (fun a => jointProb copySys leftPart a b)]
  simp only [jointProb_copySys]
  cases hB : b default <;> norm_num

/-- The two-node "copy" system has effective information `log 2` across its bipartition;
in particular effective information as defined above is not identically zero, so the vanishing
of `Φ` for disconnected systems is not a triviality. -/
theorem EI_copySys : EI copySys leftPart = Real.log 2 := by
  have hterm : ∀ (a : ↥leftPart → Bool) (b : ↥leftPartᶜ → Bool),
      jointProb copySys leftPart a b *
        Real.log (jointProb copySys leftPart a b /
          (margA copySys leftPart a * margB copySys leftPart b))
        = if a default = b default then (1 / 2) * Real.log 2 else 0 := by
    intro a b
    rw [jointProb_copySys, margA_copySys, margB_copySys]
    by_cases h : a default = b default
    · rw [if_pos h, if_pos h, show (1 : ℝ) / 2 / (1 / 2 * (1 / 2)) = 2 by norm_num]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [EI, sum_left]
  rw [sum_right (fun b => jointProb copySys leftPart (fun _ => true) b * _),
      sum_right (fun b => jointProb copySys leftPart (fun _ => false) b * _)]
  simp only [hterm]
  norm_num
  ring

lemma EI_copySys_pos : 0 < EI copySys leftPart := by
  rw [EI_copySys]
  exact Real.log_pos (by norm_num)

end Nondegenerate

end Frontier

