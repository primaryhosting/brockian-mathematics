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
## The Coffman–Kundu–Wootters monogamy inequality for three qubits

A pure state of three qubits is described by its amplitude array
`a : Fin 2 → Fin 2 → Fin 2 → ℂ`, i.e. `|ψ⟩ = ∑_{i,j,k} a i j k • |i j k⟩`
(the three tensor factors are called `A`, `B`, `C`).

* `QI.rhoA a` is the reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`.
* `QI.tangleA a = 4 · det ρ_A` is the tangle `τ_{A(BC)}`, i.e. the squared
  concurrence of the pure-state bipartition `A | BC`.
* `QI.concSqAB a` and `QI.concSqAC a` are the squared Wootters concurrences of
  the two-qubit mixed states `ρ_AB = Tr_C |ψ⟩⟨ψ|` and `ρ_AC = Tr_B |ψ⟩⟨ψ|`.

For the squared concurrences we use Wootters' singular-value description.  Since
the traced-out system is a single qubit, `ρ_AB = |u⟩⟨u| + |v⟩⟨v|` with
`u_{ij} = a i j 0` and `v_{ij} = a i j 1`, and the square roots `λ₁ ≥ λ₂ ≥ 0` of
the nonzero eigenvalues of `ρ_AB ρ̃_AB` (with `ρ̃ = (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)`)
are the singular values of the complex symmetric `2 × 2` matrix
`M = !![p, q; q, r]`, where `p = ⟨u|σ_y⊗σ_y|u*⟩`, `q = ⟨u|σ_y⊗σ_y|v*⟩`,
`r = ⟨v|σ_y⊗σ_y|v*⟩` (up to an irrelevant global sign).  Hence
`C(ρ_AB) = λ₁ - λ₂` and

`C(ρ_AB)² = λ₁² + λ₂² - 2 λ₁ λ₂ = ‖M‖_F² - 2 |det M| = ‖p‖² + 2‖q‖² + ‖r‖² - 2‖p r - q²‖`,

which is the formula taken as the definition of `QI.concSqAB` below (likewise
for `QI.concSqAC`, with the roles of `B` and `C` exchanged).

The main results are the exact residual-tangle identity `QI.residual_tangle_eq`,
`τ_{A(BC)} - C(ρ_AB)² - C(ρ_AC)² = 4 |Hdet a|`, where `Hdet` is Cayley's
hyperdeterminant of the `2 × 2 × 2` amplitude array (`4 |Hdet a|` is the
three-tangle), and the resulting CKW monogamy inequality `QI.monogamy_ckw`.

No normalisation of the state is required: both sides are homogeneous of
degree `4` in the amplitudes.
-/

namespace QI

open Complex Matrix

variable (a : Fin 2 → Fin 2 → Fin 2 → ℂ)

/-- The reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|` of the first qubit. -/

lemma tangleA_nonneg : 0 ≤ tangleA a := by
  have := concSqAB_nonneg a
  have := concSqAC_nonneg a
  have := monogamy_ckw a
  linarith

/-! ### Sanity checks: the GHZ and W states (unnormalised) -/

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
