/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Erasing one bit of information dissipates at least `k T log 2` of heat.

The setting formalised here is the standard statistical-mechanical derivation:

* the memory is a two-state system (`Bool`), initially in the uniform state
  (one bit of information, entropy `log 2`);
* the heat bath is a finite system with energies `E`, initially in the Gibbs
  state at inverse temperature `beta = 1 / (k T)`;
* system and bath are initially uncorrelated;
* the joint system is isolated, so its Shannon entropy does not decrease
  (in particular this holds, with equality, for reversible microscopic
  dynamics, i.e. for a bijection of the joint state space);
* the process is an *erasure*: the final marginal state of the memory is a
  point mass.

Then the heat `Q` absorbed by the bath is at least `k T log 2`.

The proof uses: invariance of Shannon entropy under relabelling, additivity on
product distributions, subadditivity (both consequences of Gibbs' inequality)
and the maximum-entropy property of the Gibbs state.
-/

namespace Phys

open Finset

/-- A probability distribution on a finite type. -/
structure IsProbDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a distribution on a finite type. -/

theorem shannonEntropy_subadditive {α β : Type*} [Fintype α] [Fintype β] (r : α × β → ℝ)
    (hr : IsProbDist r) :
    shannonEntropy r ≤ shannonEntropy (marg1 r) + shannonEntropy (marg2 r) := by
  have hq0 : ∀ x : α × β, 0 ≤ marg1 r x.1 * marg2 r x.2 := fun x =>
    mul_nonneg (marg1_nonneg hr x.1) (marg2_nonneg hr x.2)
  have hpos : ∀ a : α, ∀ b : β, r (a, b) ≠ 0 → 0 < marg1 r a ∧ 0 < marg2 r b := by
    intro a b hx
    have hrx : 0 < r (a, b) := lt_of_le_of_ne (hr.nonneg (a, b)) (Ne.symm hx)
    exact ⟨lt_of_lt_of_le hrx (le_marg1 hr a b), lt_of_lt_of_le hrx (le_marg2 hr a b)⟩
  have hqpos : ∀ x : α × β, r x ≠ 0 → 0 < marg1 r x.1 * marg2 r x.2 := by
    rintro ⟨a, b⟩ hx
    obtain ⟨h1, h2⟩ := hpos a b hx
    exact mul_pos h1 h2
  have hq1 : ∑ x : α × β, marg1 r x.1 * marg2 r x.2 ≤ 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul, (marg1_isProbDist hr).sum_one, (marg2_isProbDist hr).sum_one]
    norm_num
  have hmain := gibbs_ineq r (fun x => marg1 r x.1 * marg2 r x.2) hr hq0 hqpos hq1
  refine hmain.trans_eq ?_
  have key : ∀ x : α × β, -(r x * Real.log (marg1 r x.1 * marg2 r x.2))
      = -(r x * Real.log (marg1 r x.1)) + -(r x * Real.log (marg2 r x.2)) := by
    rintro ⟨a, b⟩
    rcases eq_or_ne (r (a, b)) 0 with h | h
    · simp [h]
    · obtain ⟨h1, h2⟩ := hpos a b h
      simp only
      rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]
      ring
  calc ∑ x : α × β, -(r x * Real.log (marg1 r x.1 * marg2 r x.2))
      = ∑ x : α × β, (-(r x * Real.log (marg1 r x.1)) + -(r x * Real.log (marg2 r x.2))) :=
        Finset.sum_congr rfl fun x _ => key x
    _ = (∑ x : α × β, -(r x * Real.log (marg1 r x.1)))
          + ∑ x : α × β, -(r x * Real.log (marg2 r x.2)) := Finset.sum_add_distrib
    _ = shannonEntropy (marg1 r) + shannonEntropy (marg2 r) := by
        congr 1
        · rw [Fintype.sum_prod_type, shannonEntropy]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_neg_distrib]
          show -∑ x : β, r (a, x) * Real.log (marg1 r a) = -(marg1 r a * Real.log (marg1 r a))
          rw [← Finset.sum_mul]
          rfl
        · rw [Fintype.sum_prod_type_right, shannonEntropy]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_neg_distrib]
          show -∑ x : α, r (x, b) * Real.log (marg2 r b) = -(marg2 r b * Real.log (marg2 r b))
          rw [← Finset.sum_mul]
          rfl

/-! ## The Gibbs state and its maximum-entropy property -/

section GibbsState

variable {B : Type*} [Fintype B] [Nonempty B] (E : B → ℝ) (beta : ℝ)

/-- The canonical partition function. -/
