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

lemma bwdWeight_revPath [Fintype S] (β : ℝ) (N : ℕ) (E : ℕ → S → ℝ) (T : ℕ → S → S → ℝ)
    (x : ℕ → S) :
    bwdWeight β N (revEnergy N E) (revKernel N T) (revPath N x)
      = Real.exp (-β * E N (x N)) / partitionFunction β (E N) *
          ∏ k ∈ Finset.range N, T (k + 1) (x (k + 1)) (x k) := by
  unfold bwdWeight
  have h1 : (revEnergy N E) 0 = E N := rfl
  have h2 : (revPath N x) 0 = x N := rfl
  rw [h1, h2]
  congr 1
  have hstep : ∀ k ∈ Finset.range N,
      revKernel N T k (revPath N x k) (revPath N x (k + 1))
        = (fun j => T (j + 1) (x (j + 1)) (x j)) (N - 1 - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have e1 : N - 1 - k + 1 = N - k := by omega
    have e2 : N - (k + 1) = N - 1 - k := by omega
    simp only [revKernel, revPath, e1, e2]
  rw [Finset.prod_congr rfl hstep]
  exact Finset.prod_range_reflect (fun j => T (j + 1) (x (j + 1)) (x j)) N

