/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

/-- Shannon entropy (in nats) of a finitely supported probability vector `p`.
Terms with `p x = 0` contribute `0`, since `Real.log 0 = 0`. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ x : α, -(p x * Real.log (p x))

/-- `p` is a probability distribution on the finite type `α`. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_eq_one : ∑ x : α, p x = 1

/-- A distribution is *deterministic* (a point mass) if it is concentrated on a single state. -/
def IsDeterministic {α : Type*} [Fintype α] [DecidableEq α] (q : α → ℝ) : Prop :=
  ∃ x₀ : α, ∀ x : α, q x = if x = x₀ then 1 else 0

/-! ### Entropy computations -/

/-- A point mass has zero Shannon entropy: a deterministic memory carries no uncertainty. -/
theorem shannonEntropy_eq_zero_of_isDeterministic {α : Type*} [Fintype α] [DecidableEq α]
    {q : α → ℝ} (hq : IsDeterministic q) : shannonEntropy q = 0 := by
  obtain ⟨x₀, hx₀⟩ := hq
  unfold shannonEntropy
  refine Finset.sum_eq_zero ?_
  intro x _
  rcases eq_or_ne x x₀ with h | h
  · rw [hx₀ x, if_pos h]; simp
  · rw [hx₀ x, if_neg h]; simp

/-- The uniform distribution on a two-state system (a bit) has Shannon entropy `log 2`. -/
theorem shannonEntropy_uniform_bool {p : Bool → ℝ} (hp : ∀ b : Bool, p b = 1 / 2) :
    shannonEntropy p = Real.log 2 := by
  unfold shannonEntropy
  rw [Fintype.sum_bool, hp true, hp false]
  have h : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [h]
  ring

/-! ### The entropy bound behind the Landauer limit -/

/-- Gibbs-type bound: on a finite state space of cardinality `n`, the Shannon entropy of any
probability distribution is at most `log n`.  In particular a single bit stores at most
`log 2` nats of information, so `k T log 2` is exactly the worst-case Landauer cost. -/
theorem shannonEntropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp : IsProbDist p) : shannonEntropy p ≤ Real.log (Fintype.card α) := by
  have hn : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- `H(p) - log n = ∑ p x * log (1 / (n * p x)) ≤ ∑ (1/n - p x) ≤ 0`
  have key : ∀ x : α, -(p x * Real.log (p x)) - p x * Real.log (Fintype.card α)
      ≤ 1 / (Fintype.card α : ℝ) - p x := by
    intro x
    rcases eq_or_lt_of_le (hp.nonneg x) with h | h
    · have hx : p x = 0 := h.symm
      simp only [hx, neg_zero, zero_mul, sub_zero, neg_zero, sub_self]
      positivity
    · -- `log t ≤ t - 1` with `t = 1 / (n * p x)`
      have hnp : 0 < (Fintype.card α : ℝ) * p x := mul_pos hn h
      have hlog := Real.log_le_sub_one_of_pos (x := 1 / ((Fintype.card α : ℝ) * p x))
        (by positivity)
      have hrw : Real.log (1 / ((Fintype.card α : ℝ) * p x))
          = -(Real.log (Fintype.card α) + Real.log (p x)) := by
        rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hn) (ne_of_gt h)]
      rw [hrw] at hlog
      have := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
      calc -(p x * Real.log (p x)) - p x * Real.log (Fintype.card α)
          = p x * -(Real.log (Fintype.card α) + Real.log (p x)) := by ring
        _ ≤ p x * (1 / ((Fintype.card α : ℝ) * p x) - 1) := this
        _ = 1 / (Fintype.card α : ℝ) - p x := by
              field_simp
  have hsum : shannonEntropy p - Real.log (Fintype.card α)
      ≤ ∑ _x : α, (1 / (Fintype.card α : ℝ)) - ∑ x : α, p x := by
    have hL : shannonEntropy p - Real.log (Fintype.card α)
        = ∑ x : α, (-(p x * Real.log (p x)) - p x * Real.log (Fintype.card α)) := by
      rw [Finset.sum_sub_distrib]
      unfold shannonEntropy
      rw [← Finset.sum_mul, hp.sum_eq_one, one_mul]
    rw [hL, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun x _ => key x
  have hcard : ∑ _x : α, (1 / (Fintype.card α : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [hcard, hp.sum_eq_one] at hsum
  linarith

/-! ### Landauer's principle -/

/-- **Generalized Landauer bound.**  If a process takes a system from distribution `p` to
distribution `q` while releasing heat `Q` into a reservoir at temperature `T > 0`, then the
second law (total entropy change `k * ΔS_sys + Q / T ≥ 0`) forces the heat to be at least
`k T` times the loss of Shannon entropy of the system. -/
theorem heat_ge_kT_mul_entropy_drop {α : Type*} [Fintype α]
    (k T Q : ℝ) (hT : 0 < T) (p q : α → ℝ)
    (hsecond : 0 ≤ k * (shannonEntropy q - shannonEntropy p) + Q / T) :
    k * T * (shannonEntropy p - shannonEntropy q) ≤ Q := by
  have h := mul_le_mul_of_nonneg_left hsecond (le_of_lt hT)
  have hQ : T * (Q / T) = Q := by field_simp
  nlinarith [hQ]

/-- **Landauer's principle.**  Erasing one bit of information dissipates at least `k T log 2`
of heat.

Formal content: a memory bit starts in the uniform (maximally uncertain) state `p`, and the
erasure leaves it in a deterministic state `q`.  The second law of thermodynamics, in the form
"the entropy of the system plus the Clausius entropy `Q / T` gained by the reservoir is
non-negative", then forces the dissipated heat `Q` to satisfy `Q ≥ k T log 2`. -/
theorem landauer_principle
    (k T Q : ℝ) (hT : 0 < T)
    (p q : Bool → ℝ)
    (hp : ∀ b : Bool, p b = 1 / 2)
    (hq : IsDeterministic q)
    (hsecond : 0 ≤ k * (shannonEntropy q - shannonEntropy p) + Q / T) :
    k * T * Real.log 2 ≤ Q := by
  have hpE : shannonEntropy p = Real.log 2 := shannonEntropy_uniform_bool hp
  have hqE : shannonEntropy q = 0 := shannonEntropy_eq_zero_of_isDeterministic hq
  have := heat_ge_kT_mul_entropy_drop k T Q hT p q hsecond
  rwa [hpE, hqE, sub_zero] at this

/-- The Landauer bound is tight and its hypotheses are satisfiable: for any temperature `T > 0`
there is an erasure of a uniformly random bit into the state `false` that is reversible in the
total (system + reservoir) sense and dissipates exactly `k T log 2`. -/
theorem landauer_principle_tight (k T : ℝ) (hT : 0 < T) :
    ∃ (p q : Bool → ℝ) (Q : ℝ), (∀ b : Bool, p b = 1 / 2) ∧ IsDeterministic q ∧
      0 ≤ k * (shannonEntropy q - shannonEntropy p) + Q / T ∧ Q = k * T * Real.log 2 := by
  refine ⟨fun _ => 1 / 2, fun b => if b = false then 1 else 0, k * T * Real.log 2,
    fun _ => rfl, ⟨false, fun _ => rfl⟩, ?_, rfl⟩
  have hpE : shannonEntropy (fun _ : Bool => (1 : ℝ) / 2) = Real.log 2 :=
    shannonEntropy_uniform_bool (fun _ => rfl)
  have hqE : shannonEntropy (fun b : Bool => if b = false then (1 : ℝ) else 0) = 0 :=
    shannonEntropy_eq_zero_of_isDeterministic ⟨false, fun _ => rfl⟩
  rw [hpE, hqE]
  have hdiv : k * T * Real.log 2 / T = k * Real.log 2 := by
    field_simp
  rw [hdiv]
  have hzero : k * (0 - Real.log 2) + k * Real.log 2 = 0 := by ring
  rw [hzero]

end Phys

