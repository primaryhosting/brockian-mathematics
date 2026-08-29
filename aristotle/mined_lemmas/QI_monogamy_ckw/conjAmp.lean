/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Overview

This file formalises the Coffman–Kundu–Wootters (CKW) monogamy inequality for a
pure state of three qubits:

  τ(A|BC)  ≥  τ(A|B) + τ(A|C),

where `τ` denotes the *tangle* (the square of the concurrence).

A pure three qubit state is described by its amplitude tensor
`a : Bool → Bool → Bool → ℂ`, `|ψ⟩ = ∑_{x,y,z} a x y z • |xyz⟩`.

The three tangles are expressed by their standard closed forms:

* `tangleA a = 4 · det ρ_A`, the tangle of the bipartite split `A | BC`
  (for a pure bipartite state the squared concurrence equals
  `2(1 - tr ρ_A²) = 4 det ρ_A` for a qubit `A`).

* For the two qubit *mixed* reduced states `ρ_AB` and `ρ_AC` the tangle is the
  square of Wootters' concurrence `C = max(0, λ₁ - λ₂ - λ₃ - λ₄)`, the `λᵢ`
  being the decreasingly ordered singular values of `ρ` relative to the spin
  flip.  Since `ρ_AB = ∑_c |w_c⟩⟨w_c|` with `w_c = ∑_{x,y} a x y c • |xy⟩` has
  rank at most two, only two of the `λᵢ` can be nonzero, and they are the
  singular values of the symmetric `2 × 2` matrix

      `Mc a c c' = ⟨w_c|ᵀ (σ_y ⊗ σ_y) |w_{c'}⟩`

  (indeed the nonzero eigenvalues of `ρ ρ̃` are those of `M̄ M = M† M`).
  Consequently

      `C² = (λ₁ - λ₂)² = ‖M‖_F² - 2 |det M|`,

  which is the definition `tangleAB` below; `tangleAC` is the same with the
  roles of `B` and `C` exchanged (matrix `Mb`).

The whole content of the CKW inequality is then the polynomial identity

  `‖Mc‖_F² + ‖Mb‖_F² = 4 det ρ_A`     (`frob_sum_eq`)

together with `|det M| ≥ 0`.  The difference
`τ(A|BC) - τ(A|B) - τ(A|C) = 2|det Mc| + 2|det Mb|` is the residual
(three) tangle, recorded as `ckw_residual`.

No normalisation of the amplitudes is assumed: every quantity involved is
homogeneous of degree four in the amplitudes, so the inequality holds for an
arbitrary amplitude tensor.
-/

open Complex Finset

namespace QI

/-- Amplitude tensor of a three qubit state: `|ψ⟩ = ∑ a x y z • |xyz⟩`. -/
abbrev Amp := Bool → Bool → Bool → ℂ

/-- Entrywise complex conjugate of an amplitude tensor. -/

def conjAmp (a : Amp) : Amp := fun x y z => (starRingEnd ℂ) (a x y z)

/-- The symmetric `2 × 2` matrix `⟨w_c|ᵀ (σ_y ⊗ σ_y) |w_{c'}⟩`, where
`w_c = ∑_{x,y} a x y c • |xy⟩` spans the support of `ρ_AB`. -/
