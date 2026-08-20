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
