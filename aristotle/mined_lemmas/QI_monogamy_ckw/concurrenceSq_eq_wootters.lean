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

theorem concurrenceSq_eq_wootters (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (l₁ l₂ : ℝ)
    (hl₂ : 0 ≤ l₂) (hl : l₂ ≤ l₁)
    (htr : (ρ * spinFlip ρ).trace = ((l₁ + l₂ : ℝ) : ℂ))
    (he₂ : ((ρ * spinFlip ρ).trace ^ 2 - ((ρ * spinFlip ρ) * (ρ * spinFlip ρ)).trace) / 2
      = ((l₁ * l₂ : ℝ) : ℂ)) :
    concurrenceSq ρ = (Real.sqrt l₁ - Real.sqrt l₂) ^ 2 := by
  have hl₁ : 0 ≤ l₁ := le_trans hl₂ hl
  simp only [concurrenceSq]
  rw [he₂, htr]
  simp only [Complex.ofReal_re]
  rw [Real.sqrt_mul hl₁]
  have e₁ : Real.sqrt l₁ ^ 2 = l₁ := Real.sq_sqrt hl₁
  have e₂ : Real.sqrt l₂ ^ 2 = l₂ := Real.sq_sqrt hl₂
  linear_combination -e₁ - e₂

/-- The tangle of qubit `A` against the pair `BC`, `τ_{A(BC)} = 4 det ρ_A`,
which is the squared concurrence of the pure-state bipartite cut `A | BC`. -/
