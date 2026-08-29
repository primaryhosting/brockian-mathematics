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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## A finite-sum Gibbs inequality

The nonnegativity of a Kullback–Leibler divergence between two finitely supported
probability distributions. -/

/-- One term of Gibbs' inequality: `p - q ≤ p * log (p / q)`, under the absolute
continuity assumption `q = 0 → p = 0`. -/

theorem EI_eq_zero_of_factor (sys : System V S) (A : Finset V)
    (f : ({i // i ∈ A} → S) → ({i // i ∈ A} → S) → ℝ)
    (g : ({i // i ∉ A} → S) → ({i // i ∉ A} → S) → ℝ)
    (hf : ∀ a, ∑ b, f a b = 1) (hg : ∀ a, ∑ b, g a b = 1)
    (hfac : ∀ x y, sys.tpm x y = f (resIn A x) (resIn A y) * g (resOut A x) (resOut A y)) :
    EI sys A = 0 := by
  have hzero : ∀ x : V → S, eiAt sys A x = 0 := by
    intro x
    simp only [eiAt]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [margIn_of_factor sys A f g hg hfac, margOut_of_factor sys A f g hf hfac, ← hfac x y]
    rcases eq_or_ne (sys.tpm x y) 0 with h | h
    · simp [h]
    · rw [div_self h, Real.log_one, mul_zero]
  simp [EI, hzero]

/-! ## Main theorem -/

/-- **Integrated information vanishes for a disconnected system.**
If some bipartition of the elements splits the dynamics into two independent
subsystems, then `Φ`, defined as the minimum of the effective information over all
bipartitions, is zero. -/
