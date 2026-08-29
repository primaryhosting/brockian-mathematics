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

/-!
## Setup

We formalise the discrete-time (Crooks 1998) setting.

A *protocol* of `N` steps on a finite state space `S` consists of

* a family of energy functions `E 0, E 1, …, E N : S → ℝ` (the externally controlled
  Hamiltonian at each protocol stage), and
* a family of stochastic kernels `T 0, T 1, …, T N : S → S → ℝ`, where `T k` describes
  the thermal relaxation of the system while the energy function is `E k`; each `T k`
  is assumed to satisfy *detailed balance* with respect to the Boltzmann weight of `E k`
  at inverse temperature `β`.

The **forward** experiment is: sample `x 0` from the equilibrium distribution of `E 0`;
then, for `k = 0, …, N-1`, first perform work by switching `E k ↦ E (k+1)` at frozen
configuration `x k` (this costs work `E (k+1) (x k) - E k (x k)`), and then let the system
relax `x k ↦ x (k+1)` using `T (k+1)`.

The **reverse** experiment runs the time-reversed protocol `Ẽ k = E (N - k)` with the
time-reversed kernels `T̃ k = T (N - k)`, starting from equilibrium of `Ẽ 0 = E N`, and with
each elementary step performed in the opposite order: first relax with `T̃ k`, then perform
the work `Ẽ k ↦ Ẽ (k+1)` at the (already relaxed) configuration.

This is the standard convention which makes the reverse of a forward trajectory a legal
reverse trajectory with exactly the opposite work.
-/

variable {S : Type*}

/-- Detailed balance of a kernel `K` with respect to the Boltzmann weight of the energy `E`
at inverse temperature `β`. -/

theorem micro_reversibility (β : ℝ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ)
    (hDB : ∀ k, DetailedBalance β (E k) (T k)) (x : ℕ → S) (N : ℕ) :
    Real.exp (-β * E 0 (x 0)) * ∏ k ∈ Finset.range N, T (k + 1) (x k) (x (k + 1))
      = Real.exp (β * workFwd N E x) *
          (Real.exp (-β * E N (x N)) *
            ∏ k ∈ Finset.range N, T (k + 1) (x (k + 1)) (x k)) := by
  induction N with
  | zero => simp [workFwd]
  | succ N ih =>
      have hdb := hDB (N + 1) (x N) (x (N + 1))
      -- rewrite the new forward transition using detailed balance
      have hcancel : Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E (N + 1) (x N)) = 1 := by
        rw [← Real.exp_add]
        have : β * E (N + 1) (x N) + -β * E (N + 1) (x N) = 0 := by ring
        rw [this, Real.exp_zero]
      have key : T (N + 1) (x N) (x (N + 1))
          = Real.exp (β * E (N + 1) (x N)) *
              (Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) := by
        calc T (N + 1) (x N) (x (N + 1))
            = (Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E (N + 1) (x N))) *
                T (N + 1) (x N) (x (N + 1)) := by rw [hcancel, one_mul]
          _ = Real.exp (β * E (N + 1) (x N)) *
                (Real.exp (-β * E (N + 1) (x N)) * T (N + 1) (x N) (x (N + 1))) := by ring
          _ = Real.exp (β * E (N + 1) (x N)) *
                (Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) := by
              rw [hdb]
      have hwork : Real.exp (β * workFwd (N + 1) E x)
          = Real.exp (β * workFwd N E x) *
              (Real.exp (β * E (N + 1) (x N)) * Real.exp (-β * E N (x N))) := by
        rw [workFwd, Finset.sum_range_succ, ← workFwd, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [Finset.prod_range_succ, Finset.prod_range_succ, hwork, key]
      linear_combination (Real.exp (β * E (N + 1) (x N)) *
        Real.exp (-β * E (N + 1) (x (N + 1))) * T (N + 1) (x (N + 1)) (x N)) * ih

/-!
## Rewriting the reverse weight in terms of the forward trajectory
-/

