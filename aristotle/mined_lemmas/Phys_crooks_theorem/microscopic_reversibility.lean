import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
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

/-- A driven microscopic system on a finite state space, observed at times
`0, 1, …, N`.

* `E k` is the energy function of the system after the `k`-th update of the
  external protocol parameter.
* `T k x y` is the probability that the thermalisation step performed while the
  energy function is `E k` takes the system from `x` to `y`.  It is assumed to
  satisfy *detailed balance* with respect to the Boltzmann weights of `E k` at
  inverse temperature `beta`.

A forward trajectory is a sequence of states `x₀, x₁, …, x_N`: the system starts
in thermal equilibrium for `E 0`, then alternately the protocol is advanced
(`E k → E (k+1)`, which costs work) and the system relaxes with the kernel
`T (k+1)`. -/
structure CrooksSystem where
  /-- the (finite, nonempty) microscopic state space -/
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  [neS : Nonempty S]
  /-- number of protocol steps -/
  N : ℕ
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  /-- energy function after `k` protocol updates -/
  E : ℕ → S → ℝ
  /-- thermalisation kernel used while the energy is `E k` -/
  T : ℕ → S → S → ℝ
  /-- detailed balance of `T k` with respect to the Boltzmann weights of `E k` -/
  detailed_balance : ∀ (k : ℕ) (x y : S),
    Real.exp (-beta * E k x) * T k x y = Real.exp (-beta * E k y) * T k y x

attribute [instance] CrooksSystem.finS CrooksSystem.decS CrooksSystem.neS

variable (C : CrooksSystem)

/-- Partition function of the equilibrium state with energy `E k`. -/

theorem microscopic_reversibility (γ : ℕ → C.S) :
    probF C γ
      = Real.exp (C.beta * (work C γ - deltaF C)) * probR C (fun k => γ (C.N - k)) := by
  have hZ0 : partition C 0 ≠ 0 := (partition_pos C 0).ne'
  have hZN : partition C C.N ≠ 0 := (partition_pos C C.N).ne'
  -- detailed balance in ratio form
  have hDB : ∀ (k : ℕ) (x y : C.S),
      C.T k x y = Real.exp (C.beta * (C.E k x - C.E k y)) * C.T k y x := by
    intro k x y
    have hx : Real.exp (-C.beta * C.E k x) ≠ 0 := (Real.exp_pos _).ne'
    refine mul_left_cancel₀ hx ?_
    rw [C.detailed_balance k x y, ← mul_assoc, ← Real.exp_add]
    ring_nf
  -- rewrite the forward product in terms of the backward one
  have hprod : ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ k) (γ (k + 1))
      = (∏ k ∈ Finset.range C.N,
          Real.exp (C.beta * (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))))
        * ∏ k ∈ Finset.range C.N, C.T (k + 1) (γ (k + 1)) (γ k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => hDB _ _ _)
  have hexpprod : (∏ k ∈ Finset.range C.N,
      Real.exp (C.beta * (C.E (k + 1) (γ k) - C.E (k + 1) (γ (k + 1)))))
      = Real.exp (C.beta * (work C γ + C.E 0 (γ 0) - C.E C.N (γ C.N))) := by
    rw [← Real.exp_sum, ← Finset.mul_sum, sum_energy_diff C γ]
  have hexp : Real.exp (C.beta * (work C γ - deltaF C))
      = Real.exp (C.beta * work C γ) * (partition C C.N / partition C 0) := by
    rw [← exp_neg_beta_deltaF C, ← Real.exp_add]
    ring_nf
  have e1 : Real.exp (C.beta * (work C γ + C.E 0 (γ 0) - C.E C.N (γ C.N)))
      * Real.exp (-(C.beta * C.E 0 (γ 0)))
      = Real.exp (C.beta * work C γ) * Real.exp (-(C.beta * C.E C.N (γ C.N))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  unfold probF probR
  simp only [Nat.sub_zero]
  rw [prod_rev C γ, hprod, hexpprod, hexp]
  field_simp
  linear_combination (∏ k ∈ Finset.range C.N, C.T (k + 1) (γ (k + 1)) (γ k)) * e1

/-! ### Work of the reversed trajectory -/

