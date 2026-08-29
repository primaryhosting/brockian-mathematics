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

lemma sum_filter_involution {Ω : Type*} [Fintype Ω] (R : Ω → Ω) (hR : ∀ ω, R (R ω) = ω)
    (WF WR PF PR : Ω → ℝ) (g : ℝ → ℝ) (w : ℝ)
    (hW : ∀ ω, WR (R ω) = -WF ω)
    (hP : ∀ ω, PF ω = g (WF ω) * PR (R ω)) :
    ∑ ω ∈ Finset.univ.filter (fun ω => WF ω = w), PF ω
      = g w * ∑ η ∈ Finset.univ.filter (fun η => WR η = -w), PR η := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (i := fun ω => R ω) (j := fun η => R η) ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rw [hW ω, hω]
  · intro η hη
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
    have : WR (R (R η)) = -WF (R η) := hW (R η)
    rw [hR η] at this
    rw [hη] at this
    linarith
  · intro ω _; exact hR ω
  · intro η _; exact hR η
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hP ω, hω]

/-- The trajectory space of an `N`-step protocol: `N+1` successive configurations. -/
abbrev Traj (S : Type*) (N : ℕ) : Type _ := Fin (N + 1) → S

/-- A trajectory viewed as a function `ℕ → S` (constant past the final time). -/
