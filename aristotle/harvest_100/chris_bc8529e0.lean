import Mathlib

/-!
# Integrated information `Φ` and disconnected systems

This file gives a self-contained formalization of integrated information `Φ`
(as in Integrated Information Theory) for a finite system of binary nodes whose
dynamics are given by a *mechanism*: for each node `i`, a conditional
probability `prob i s b` of node `i` taking value `b` at the next time step,
given the current global state `s`.

* `Frontier.Mechanism.kernel` is the induced transition kernel on global states,
  `T(s, t) = ∏ i, prob i s (t i)`.
* Given a bipartition `(S, Sᶜ)`, `Frontier.Mechanism.cutKernel` is the kernel of
  the *cut* system in which every node only reads the inputs on its own side of
  the partition, the inputs coming from the other side being replaced by uniform
  independent noise.
* `Frontier.Mechanism.EI` is the effective information of a bipartition: the
  Kullback–Leibler divergence between the true kernel and the cut kernel,
  averaged over the uniform distribution of current states.
* `Frontier.Mechanism.Phi` is `Φ`, the minimum of `EI` over all nontrivial
  bipartitions.

The main theorem `Frontier.iit_phi_partition` states that a *disconnected*
system — one admitting a nontrivial bipartition across which no node reads any
input — has `Φ = 0`.
-/

open scoped BigOperators

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A global state of the system: a Boolean value at each node. -/
abbrev State (V : Type*) : Type _ := V → Bool

/-- A *mechanism* on the finite set of nodes `V`: for each node `i`, current
global state `s` and Boolean `b`, the probability `prob i s b` that node `i`
takes the value `b` at the next time step.  Nodes update independently given the
current state.  Probabilities are assumed strictly positive (a noisy system). -/
structure Mechanism (V : Type*) [Fintype V] where
  /-- probability that node `i` is `b` at the next step, given current state `s`. -/
  prob : V → State V → Bool → ℝ
  /-- the dynamics is noisy: all transition probabilities are strictly positive. -/
  pos : ∀ i s b, 0 < prob i s b
  /-- each node's update is a probability distribution on `Bool`. -/
  normalized : ∀ i s, ∑ b : Bool, prob i s b = 1

namespace Mechanism

variable (M : Mechanism V)

/-- The transition kernel of the whole system: nodes update independently. -/
noncomputable def kernel (s t : State V) : ℝ := ∏ i, M.prob i s (t i)

/-- The state obtained from `s` by keeping the values on the side of the
bipartition `{S, Sᶜ}` containing `i`, and replacing the values on the other side
by the noise `u`. -/
def splice (S : Finset V) (i : V) (s u : State V) : State V :=
  fun j => if (i ∈ S ↔ j ∈ S) then s j else u j

/-- The mechanism of node `i` in the system *cut* along the bipartition
`{S, Sᶜ}`: the inputs of `i` coming from the other side of the partition are
replaced by independent uniform noise. -/
noncomputable def cutProb (S : Finset V) (i : V) (s : State V) (b : Bool) : ℝ :=
  (Fintype.card (State V) : ℝ)⁻¹ * ∑ u : State V, M.prob i (splice S i s u) b

/-- The transition kernel of the system cut along the bipartition `{S, Sᶜ}`. -/
noncomputable def cutKernel (S : Finset V) (s t : State V) : ℝ :=
  ∏ i, M.cutProb S i s (t i)

/-- The effective information of the bipartition `{S, Sᶜ}`: the
Kullback–Leibler divergence of the cut kernel from the true kernel, averaged
over the uniform distribution on current states. -/
noncomputable def EI (S : Finset V) : ℝ :=
  (Fintype.card (State V) : ℝ)⁻¹ *
    ∑ s : State V, ∑ t : State V,
      M.kernel s t * Real.log (M.kernel s t / M.cutKernel S s t)

/-- The type of nontrivial bipartitions of the system, indexed by one of the two
sides. -/
abbrev Bipartition (V : Type*) [Fintype V] [DecidableEq V] : Type _ :=
  {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ}

/-- Integrated information `Φ`: the minimum of the effective information over
all nontrivial bipartitions of the system. -/
noncomputable def Phi : ℝ := ⨅ S : Bipartition V, M.EI S.1

/-- A system is *disconnected* along the bipartition `{S, Sᶜ}` if the mechanism
of every node depends only on the current values of the nodes lying on the same
side of the bipartition: there are no causal connections across the cut. -/
def Disconnected (S : Finset V) : Prop :=
  ∀ i : V, ∀ s s' : State V,
    (∀ j, (i ∈ S ↔ j ∈ S) → s j = s' j) → ∀ b, M.prob i s b = M.prob i s' b

end Mechanism

/-! ### Gibbs' inequality -/

/-- Gibbs' inequality (nonnegativity of the Kullback–Leibler divergence) for
finitely supported probability distributions, with `q` strictly positive. -/
theorem klDiv_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 < q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by
  have key : ∀ a, -(p a * Real.log (p a / q a)) ≤ q a - p a := by
    intro a
    rcases eq_or_lt_of_le (hp a) with h | h
    · simp [← h, (hq a).le]
    · have hlog : Real.log (p a / q a) = -Real.log (q a / p a) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [hlog]
      have hx : (0:ℝ) < q a / p a := div_pos (hq a) h
      have := Real.log_le_sub_one_of_pos hx
      have hmul : p a * Real.log (q a / p a) ≤ p a * (q a / p a - 1) :=
        mul_le_mul_of_nonneg_left this h.le
      have heq : p a * (q a / p a - 1) = q a - p a := by field_simp
      linarith
  have hsum : ∑ a, -(p a * Real.log (p a / q a)) ≤ ∑ a, (q a - p a) :=
    Finset.sum_le_sum fun a _ => key a
  rw [Finset.sum_sub_distrib, hp1, hq1] at hsum
  simp only [Finset.sum_neg_distrib] at hsum
  linarith

/-! ### Basic positivity and normalization facts -/

namespace Mechanism

variable (M : Mechanism V)

omit [DecidableEq V] in
theorem kernel_pos (s t : State V) : 0 < M.kernel s t :=
  Finset.prod_pos fun i _ => M.pos i s (t i)

theorem cutProb_pos (S : Finset V) (i : V) (s : State V) (b : Bool) :
    0 < M.cutProb S i s b := by
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos (fun u _ => M.pos _ _ _) ?_
  exact Finset.univ_nonempty

theorem cutKernel_pos (S : Finset V) (s t : State V) : 0 < M.cutKernel S s t :=
  Finset.prod_pos fun i _ => M.cutProb_pos S i s (t i)

theorem cutProb_normalized (S : Finset V) (i : V) (s : State V) :
    ∑ b : Bool, M.cutProb S i s b = 1 := by
  have hcard : (0:ℝ) < (Fintype.card (State V) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [cutProb, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [M.normalized]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

/-- Any independent-node kernel with normalized single-node distributions is a
probability distribution on global states. -/
theorem sum_prod_eq_one (f : V → Bool → ℝ) (hf : ∀ i, ∑ b : Bool, f i b = 1) :
    ∑ t : State V, ∏ i, f i (t i) = 1 := by
  have := Finset.prod_univ_sum (fun _ : V => (Finset.univ : Finset Bool)) f
  rw [Fintype.piFinset_univ] at this
  simp only [hf, Finset.prod_const_one] at this
  exact this.symm

theorem kernel_normalized (s : State V) : ∑ t : State V, M.kernel s t = 1 :=
  sum_prod_eq_one (fun i b => M.prob i s b) (fun i => M.normalized i s)

theorem cutKernel_normalized (S : Finset V) (s : State V) :
    ∑ t : State V, M.cutKernel S s t = 1 :=
  sum_prod_eq_one (fun i b => M.cutProb S i s b) (fun i => M.cutProb_normalized S i s)

/-- Effective information is nonnegative, for every bipartition. -/
theorem EI_nonneg (S : Finset V) : 0 ≤ M.EI S := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => ?_)
  exact klDiv_nonneg _ _ (fun t => (M.kernel_pos s t).le)
    (fun t => M.cutKernel_pos S s t) (M.kernel_normalized s) (M.cutKernel_normalized S s)

/-- Across a cut along which the system is disconnected, the cut mechanism
coincides with the original mechanism. -/
theorem cutProb_eq_prob_of_disconnected {S : Finset V} (h : M.Disconnected S)
    (i : V) (s : State V) (b : Bool) : M.cutProb S i s b = M.prob i s b := by
  have hcard : (Fintype.card (State V) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hterm : ∀ u : State V, M.prob i (splice S i s u) b = M.prob i s b := by
    intro u
    refine h i _ s (fun j hj => ?_) b
    simp [splice, hj]
  simp only [cutProb, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem EI_eq_zero_of_disconnected {S : Finset V} (h : M.Disconnected S) : M.EI S = 0 := by
  have hker : ∀ s t : State V, M.cutKernel S s t = M.kernel s t := by
    intro s t
    simp only [cutKernel, kernel, M.cutProb_eq_prob_of_disconnected h]
  simp only [EI, hker, div_self (M.kernel_pos _ _).ne', Real.log_one, mul_zero,
    Finset.sum_const_zero, mul_zero]

end Mechanism

/-- **Integrated information of a disconnected system vanishes.**

If a finite system of noisy binary nodes admits a nontrivial bipartition
`{S, Sᶜ}` across which no node reads any input (`M.Disconnected S`), then its
integrated information `Φ`, defined as the minimum over all nontrivial
bipartitions of the effective information (the Kullback–Leibler divergence
between the true transition kernel and the kernel of the system cut along that
bipartition), is zero. -/
theorem iit_phi_partition (M : Mechanism V) (S : Finset V)
    (hS : S.Nonempty) (hSne : S ≠ Finset.univ) (hdis : M.Disconnected S) :
    M.Phi = 0 := by
  have hne : Nonempty (Mechanism.Bipartition V) := ⟨⟨S, hS, hSne⟩⟩
  have hbdd : BddBelow (Set.range fun S : Mechanism.Bipartition V => M.EI S.1) :=
    (Set.finite_range _).bddBelow
  refine le_antisymm ?_ ?_
  · have := ciInf_le hbdd (⟨S, hS, hSne⟩ : Mechanism.Bipartition V)
    rw [M.EI_eq_zero_of_disconnected hdis] at this
    exact this
  · exact le_ciInf fun T => M.EI_nonneg T.1

/-! ### Sanity checks: the definitions are not degenerate

We exhibit two concrete two-node systems (nodes indexed by `Bool`).  The first
is disconnected, so the main theorem applies to it; the second is a pair of
mutually copying nodes, for which cutting a bipartition really does change the
mechanism. -/

/-- Two independent noisy nodes: each node is refreshed to a uniformly random
value, irrespective of the current state. -/
noncomputable def independentMech : Mechanism Bool where
  prob _ _ _ := 1 / 2
  pos := by intro i s b; norm_num
  normalized := by intro i s; simp

theorem independentMech_disconnected :
    independentMech.Disconnected {false} := by
  intro i s s' _ b
  rfl

/-- The main theorem applied to a concrete disconnected two-node system. -/
theorem independentMech_phi_eq_zero : independentMech.Phi = 0 := by
  refine iit_phi_partition independentMech {false} ⟨false, by simp⟩ ?_
    independentMech_disconnected
  intro h
  have : (true : Bool) ∈ ({false} : Finset Bool) := by rw [h]; simp
  simp at this

/-- Two nodes copying each other, with noise: node `i` takes the current value
of the other node with probability `3/4`. -/
noncomputable def copyMech : Mechanism Bool where
  prob i s b := if b = s (!i) then 3 / 4 else 1 / 4
  pos := by intro i s b; split <;> norm_num
  normalized := by
    intro i s
    simp only [Fintype.sum_bool]
    cases s (!i) <;> norm_num

/-- Cutting the bipartition `{{false}, {true}}` genuinely modifies the mechanism
of the mutually copying system: the cut node sees only noise. -/
theorem copyMech_cutProb_ne_prob :
    copyMech.cutProb {false} false (fun _ => true) true ≠
      copyMech.prob false (fun _ => true) true := by
  have h1 : copyMech.cutProb {false} false (fun _ => true) true = 1 / 2 := by
    simp only [Mechanism.cutProb, copyMech, Mechanism.splice]
    rw [show (Finset.univ : Finset (Bool → Bool)) =
        {(fun _ => false), (fun _ => true), id, not} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
  have h2 : copyMech.prob false (fun _ => true) true = 3 / 4 := by
    simp [copyMech]
  rw [h1, h2]
  norm_num

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

