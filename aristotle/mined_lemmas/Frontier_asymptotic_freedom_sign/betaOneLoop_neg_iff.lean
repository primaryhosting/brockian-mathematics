import Mathlib

/-!
# Asymptotic Freedom Sign
Category: Frontier Physics
Target: Frontier.asymptotic_freedom_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to be the very first commands in a file,
-- so the module header comment above is placed immediately after the import.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The one-loop beta-function coefficient for an `SU(N)` gauge theory with `nf`
Dirac fermions in the fundamental representation:
`b₀ = 11 N / 3 - 2 nf / 3`. -/

theorem betaOneLoop_neg_iff (N nf : ℕ) (g : ℝ) (hg : 0 < g) :
    betaOneLoop N nf g < 0 ↔ 2 * nf < 11 * N := by
  have hden : 0 < 16 * Real.pi ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  rw [betaOneLoop, div_neg_iff]
  constructor
  · rintro (⟨-, hd⟩ | ⟨hnum, -⟩)
    · linarith
    · have hb : 0 < b0 N nf := by nlinarith
      have h : (2 * nf : ℝ) < 11 * N := by
        rw [b0] at hb; linarith
      exact_mod_cast h
  · intro hnf
    have h : (2 * nf : ℝ) < 11 * N := by exact_mod_cast hnf
    have hb : 0 < b0 N nf := by rw [b0]; linarith
    exact Or.inr ⟨by nlinarith, hden⟩

/-- The special case of QCD: `SU(3)` with six quark flavours. -/
