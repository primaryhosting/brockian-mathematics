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

set_option grind.warning false

/-!
## Overview

This file formalises the *sharpness of the phase transition* for the ferromagnetic Ising
model, in the form established by Duminil-Copin (with Tassion): below the critical
inverse temperature the two-point function decays exponentially fast, while above it the
two-point function does not tend to zero.  There is no intermediate regime.

The development is organised as follows.

* `Frontier.IsingBox` : a finite volume ferromagnetic Ising model, with an explicit
  Gibbs weight, partition function, expectation and two-point function.  We prove the
  basic structural facts: the partition function is positive, expectations of bounded
  observables are bounded, the two-point function is bounded by `1` and is a
  differentiable function of the inverse temperature, the spontaneous magnetisation with
  free boundary conditions vanishes (global spin-flip symmetry) and the two-point
  function vanishes at `β = 0` (single-site spin-flip symmetry).

* `Frontier.gronwall_bound` : the analytic heart of the Duminil-Copin–Tassion argument.
  From the differential inequality
  `n * θ n s ≤ (∑ k < n, θ k s) * (θ n)' s`
  one deduces, by integrating the logarithmic derivative, the quantitative bound
  `θ n β ≤ exp ( - (β' - β) * n / ∑ k < n, θ k β')` for `β < β'`.

* `Frontier.exp_decay_of_bounded_sums` : if in addition the partial sums
  `∑ k < n, θ k β'` are bounded, the previous bound is genuine exponential decay.

* `Frontier.IsingSharpnessSetup` : the Ising two-point functions of a sequence of finite
  volumes, together with the two monotonicity/positivity inputs (Griffiths' inequalities)
  and the Duminil-Copin–Tassion differential inequality (the deep input coming from the
  random-current representation, which is taken as a hypothesis here).

* `Frontier.duminil_ising_sharp` : the sharpness dichotomy for the critical parameter
  `Frontier.IsingSharpnessSetup.betaC`.

Finally `Frontier.trivialSetup` exhibits a concrete `IsingSharpnessSetup`, so that the
hypotheses of the main theorem are consistent.
-/

namespace Frontier

/-! ## Spins and spin flips -/

/-- The real value `±1` of a Boolean spin variable. -/

lemma sum_flipAll_zero (x : S) (w : (S → Bool) → ℝ) (hw : ∀ σ, w (flipAll σ) = w σ) :
    ∑ σ : S → Bool, spin (σ x) * w σ = 0 := by
  set F : (S → Bool) → ℝ := fun σ => spin (σ x) * w σ with hF
  have h1 : ∑ σ : S → Bool, F σ = ∑ σ : S → Bool, F (flipAllEquiv σ) :=
    (Equiv.sum_comp (flipAllEquiv) F).symm
  have h2 : ∀ σ : S → Bool, F (flipAllEquiv σ) = - F σ := by
    intro σ
    simp only [hF, flipAllEquiv, Function.Involutive.coe_toPerm, flipAll, hw σ, spin_not]
    ring
  have h3 : ∑ σ : S → Bool, F (flipAllEquiv σ) = - ∑ σ : S → Bool, F σ := by
    simp only [h2, Finset.sum_neg_distrib]
  rw [h3] at h1
  linarith

end Flips

/-! ## Finite volume Ising models -/

/-- A finite volume ferromagnetic Ising model: a finite set of sites, a symmetric
nonnegative coupling constant `J`, and two marked sites `o ≠ t` (the origin and the
"far away" site whose correlation with the origin we study). -/
structure IsingBox where
  /-- The (finite) set of sites of the box. -/
  site : Type
  [siteFintype : Fintype site]
  [siteDecEq : DecidableEq site]
  /-- The coupling constants. -/
  J : site → site → ℝ
  /-- The couplings are symmetric. -/
  J_symm : ∀ x y, J x y = J y x
  /-- Ferromagnetic couplings. -/
  J_nonneg : ∀ x y, 0 ≤ J x y
  /-- The origin. -/
  o : site
  /-- The marked "far" site. -/
  t : site
  /-- The two marked sites are distinct. -/
  o_ne_t : o ≠ t

attribute [instance] IsingBox.siteFintype IsingBox.siteDecEq

namespace IsingBox

variable (M : IsingBox)

/-- The Ising energy of a configuration (free boundary conditions). -/
