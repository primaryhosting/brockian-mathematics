/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

lemma sum_ramp_sq {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) (y : BV n) :
    ∑ v : BV n, (ramp f y v) ^ 2 = 2 ^ n * (1 + rsgn (dot s y)) := by
  classical
  have hstep1 : ∀ v : BV n, (ramp f y v) ^ 2
      = ∑ x : BV n, ∑ x' : BV n,
          (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
          (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0)) := by
    intro v
    rw [sq, ramp, Finset.sum_mul_sum]
  simp only [hstep1]
  rw [Finset.sum_comm]
  have hstep2 : ∀ x : BV n, ∑ v : BV n, ∑ x' : BV n,
      (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
      (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0))
      = ∑ x' : BV n, rsgn (dot x y) * rsgn (dot x' y) * (if f x = f x' then (1:ℝ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    have : ∀ v : BV n,
        (rsgn (dot x y) * (if f x = v then (1:ℝ) else 0)) *
        (rsgn (dot x' y) * (if f x' = v then (1:ℝ) else 0))
        = (rsgn (dot x y) * rsgn (dot x' y)) *
            ((if f x = v then (1:ℝ) else 0) * (if f x' = v then (1:ℝ) else 0)) := by
      intro v; ring
    simp only [this]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single (f x)]
    · by_cases hx : f x' = f x
      · simp [hx]
      · simp [hx, Ne.symm hx]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_univ (f x)) hb
  simp only [hstep2]
  have hstep3 : ∀ x : BV n,
      ∑ x' : BV n, rsgn (dot x y) * rsgn (dot x' y) * (if f x = f x' then (1:ℝ) else 0)
      = 1 + rsgn (dot s y) := by
    intro x
    have hcond : ∀ x' : BV n, (if f x = f x' then (1:ℝ) else 0)
        = if x' ∈ ({x, x + s} : Finset (BV n)) then (1:ℝ) else 0 := by
      intro x'
      have : (f x = f x') ↔ (x' ∈ ({x, x + s} : Finset (BV n))) := by
        rw [h.fibre x x']
        simp [Finset.mem_insert, Finset.mem_singleton]
      simp only [this]
    simp only [hcond, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hne : x ≠ x + s := by
      intro hc
      apply h.ne_zero
      have := congrArg (fun w => w + x) hc
      simpa [add_comm, add_left_comm, add_assoc] using this.symm
    rw [Finset.sum_pair hne]
    rw [dot_add_left, rsgn_add]
    rw [← mul_assoc, rsgn_mul_self]
    ring
  simp only [hstep3]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card, Fintype.card_fun,
    Fintype.card_fin]
  push_cast
  ring

/-- **Simon's algorithm, quantum part.**  With a single oracle query, the measured value `y` is
uniformly distributed over the `2ⁿ⁻¹` vectors orthogonal to the hidden period `s`. -/
