/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

theorem le_pow_div_of_recursive_bound (a : ℕ → ℝ) (L : ℕ) (hL : 0 < L) (c : ℝ) (hc0 : 0 ≤ c)
    (ha1 : ∀ n, a n ≤ 1) (hrec : ∀ n, a (n + L) ≤ c * a n) :
    ∀ n, a n ≤ c ^ (n / L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < L
    · rw [Nat.div_eq_of_lt h, pow_zero]
      exact ha1 n
    · push_neg at h
      have hn : n - L + L = n := Nat.sub_add_cancel h
      have h1 : a n ≤ c * a (n - L) := by
        have := hrec (n - L)
        rwa [hn] at this
      have h2 : a (n - L) ≤ c ^ ((n - L) / L) := ih _ (by omega)
      have h3 : c * a (n - L) ≤ c * c ^ ((n - L) / L) := mul_le_mul_of_nonneg_left h2 hc0
      have hdiv : n / L = (n - L) / L + 1 := Nat.div_eq_sub_div hL h
      calc a n ≤ c * c ^ ((n - L) / L) := le_trans h1 h3
        _ = c ^ ((n - L) / L + 1) := by ring
        _ = c ^ (n / L) := by rw [hdiv]

/-- **Exponential decay from the subcritical recursion.** This is the analytic core of the
subcritical half of sharpness: the Duminil-Copin–Tassion finite-criterion `φ_β(S) < 1`
produces exactly such a contraction for the two-point function, and it upgrades to genuine
exponential decay. -/
