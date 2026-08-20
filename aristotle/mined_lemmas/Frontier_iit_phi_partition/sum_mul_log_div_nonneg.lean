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

namespace Frontier

/-! ## Gibbs' inequality (nonnegativity of relative entropy) -/

/-- Gibbs' inequality on a finite index type: the relative entropy (Kullback–Leibler
divergence) of two probability distributions is nonnegative, provided `p` is absolutely
continuous with respect to `q`. -/

theorem sum_mul_log_div_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, 0 < p i → 0 < q i)
    (hsp : ∑ i, p i = 1) (hsq : ∑ i, q i = 1) :
    0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  have key : ∀ i, p i * Real.log (q i / p i) ≤ q i - p i := by
    intro i
    rcases (hp i).lt_or_eq with h | h
    · have hqi := hac i h
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqi h)
      calc p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
            mul_le_mul_of_nonneg_left hlog h.le
        _ = q i - p i := by field_simp
    · rw [← h]
      simpa using hq i
  have hsum : ∑ i, p i * Real.log (q i / p i) ≤ 0 := by
    calc ∑ i, p i * Real.log (q i / p i) ≤ ∑ i, (q i - p i) :=
          Finset.sum_le_sum fun i _ => key i
      _ = 0 := by rw [Finset.sum_sub_distrib, hsp, hsq, sub_self]
  have heq : ∑ i, p i * Real.log (p i / q i) = -∑ i, p i * Real.log (q i / p i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show p i / q i = (q i / p i)⁻¹ from (inv_div _ _).symm, Real.log_inv]
    ring
  rw [heq]
  linarith

/-! ## Systems, mechanisms and the cut (partitioned) dynamics -/

/-- A finite discrete dynamical system: `V` is the set of elements (nodes), `S` the set of
states of a single element, and `tpm v s t` is the probability that element `v` is in state
`t` at the next time step, given that the whole system is in state `s` now.  Elements update
independently of each other given the current global state (this is the standard
transition-probability-matrix setting used in integrated information theory). -/
structure System (V S : Type*) [Fintype V] [DecidableEq V] [Fintype S] where
  /-- `tpm v s t`: probability that node `v` transitions to state `t` from global state `s`. -/
  tpm : V → (V → S) → S → ℝ
  tpm_nonneg : ∀ v s t, 0 ≤ tpm v s t
  tpm_sum : ∀ v s, ∑ t, tpm v s t = 1

namespace System

variable {V S : Type*} [Fintype V] [DecidableEq V] [Fintype S] [Nonempty S]

/-- The joint transition probability of the whole system: the probability of the next global
state `s'` given the current global state `s`. -/
