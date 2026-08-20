import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any comment, so the header block above sits
directly after the single `import Mathlib` line.)
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

open Matrix Complex

/-- Amplitudes of a pure state of three qubits `A`, `B`, `C`:
`ψ i j k` is the coefficient of the computational basis vector `|i j k⟩`. -/
abbrev Amp : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`, i.e. `Tr_{BC} |ψ⟩⟨ψ|`. -/

noncomputable def spinFlip (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  YY * ρ.map (starRingEnd ℂ) * YY

/-- The squared Wootters concurrence of a two-qubit density matrix of rank at most two.

Wootters' concurrence is `C(ρ) = max (0, √λ₁ - √λ₂ - √λ₃ - √λ₄)`, where the `λᵢ` are the
(real, nonnegative) eigenvalues of `M = ρ ρ̃` in decreasing order.  When `ρ` has rank at most
two — which is the case for the two-party marginals of a pure three-qubit state — one has
`λ₃ = λ₄ = 0`, hence
`C(ρ)² = (√λ₁ - √λ₂)² = (λ₁ + λ₂) - 2√(λ₁λ₂) = tr M - 2√(e₂ M)`,
where `e₂ M = (tr M ^ 2 - tr (M ^ 2)) / 2` is the second elementary symmetric function of the
eigenvalues of `M`.  This is the formula used as the definition here. -/
