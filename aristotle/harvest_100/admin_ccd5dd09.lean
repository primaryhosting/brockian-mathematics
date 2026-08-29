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
noncomputable def b0 (N nf : ℕ) : ℝ := 11 * (N : ℝ) / 3 - 2 * (nf : ℝ) / 3

/-- The one-loop renormalization-group beta function
`β(g) = - b₀ g³ / (16 π²)`. -/
noncomputable def betaOneLoop (N nf : ℕ) (g : ℝ) : ℝ :=
    -(b0 N nf) * g ^ 3 / (16 * Real.pi ^ 2)

/-- **Asymptotic freedom sign.**  For an `SU(N)` gauge theory with `N ≥ 2` colours and
`nf` fundamental Dirac fermion flavours satisfying `2 nf < 11 N` (e.g. QCD, `N = 3`,
`nf ≤ 16`), the one-loop beta function is strictly negative at any positive coupling
`g > 0`: the coupling decreases with increasing energy scale.

The hypothesis `2 ≤ N` records that the gauge group is non-abelian; it is not needed
for the inequality itself, which follows from `2 nf < 11 N` alone. -/
theorem asymptotic_freedom_sign (N nf : ℕ) (_hN : 2 ≤ N) (hnf : 2 * nf < 11 * N)
    (g : ℝ) (hg : 0 < g) : betaOneLoop N nf g < 0 := by
  have hb : 0 < b0 N nf := by
    have h : (2 * nf : ℝ) < 11 * N := by exact_mod_cast hnf
    unfold b0
    push_cast at h ⊢
    linarith
  have hden : 0 < 16 * Real.pi ^ 2 := by positivity
  have hg3 : 0 < g ^ 3 := by positivity
  unfold betaOneLoop
  apply div_neg_of_neg_of_pos _ hden
  nlinarith

/-- Sharp characterisation: at positive coupling the one-loop beta function is negative
exactly when the flavour count obeys the asymptotic-freedom bound `2 nf < 11 N`. -/
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
theorem asymptotic_freedom_sign_qcd (g : ℝ) (hg : 0 < g) : betaOneLoop 3 6 g < 0 :=
  asymptotic_freedom_sign 3 6 (by norm_num) (by norm_num) g hg

end Frontier

