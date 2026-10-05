/-
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Modularity
Category: Frontier Math
Target: Math2.modularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalises the statement of the modularity theorem (Taniyama–Shimura–Wiles)
for elliptic curves over `ℚ`, given by integral Weierstrass models, together with a
fully kernel-checked numerical verification of the modularity prediction for the
elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, whose associated newform is the
eta product `η(z)² η(11z)²`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math2

open WeierstrassCurve CongruenceSubgroup MatrixGroups ModularFormClass UpperHalfPlane

/-! ## Point counts of the reductions of a Weierstrass model -/

/-- The number of points of the reduction mod `p` of an integral Weierstrass model `W`:
the affine solutions of the Weierstrass equation over `ℤ/p`, plus the point at infinity.
(For `p = 0` this is junk, and it is only used for primes of good reduction.) -/

noncomputable def cardPoints (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card {q : ZMod p × ZMod p //
    (W.map (Int.castRingHom (ZMod p))).toAffine.Equation q.1 q.2} + 1

/-- The trace of Frobenius `a_p = p + 1 - #E(𝔽_p)` of an integral Weierstrass model. -/

noncomputable def ap (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ := (p : ℤ) + 1 - cardPoints W p

/-! ## The statement of modularity -/

/-- An integral Weierstrass model `W` is *modular* if there is a level `N ≥ 1` and a
weight-two cusp form `f` for `Γ₀(N)`, normalised so that its first `q`-expansion
coefficient is `1`, whose `p`-th `q`-expansion coefficient equals the trace of Frobenius
`a_p(W)` for every prime `p` not dividing `N` and of good reduction.

Equivalently, the `L`-series of the curve is the Mellin transform of a weight-two cusp
form of level `N`; by strong multiplicity one, prescribing the coefficients at the
primes away from `N` and from the discriminant determines the situation. -/

def IsModular (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2,
    (qExpansion 1 (f : ℍ → ℂ)).coeff 1 = 1 ∧
      ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ (N : ℤ) * W.Δ) →
        (qExpansion 1 (f : ℍ → ℂ)).coeff p = (ap W p : ℂ)

/-- **The modularity theorem** (Taniyama–Shimura–Wiles), as a statement: every elliptic
curve over `ℚ` — equivalently, every nonsingular integral Weierstrass model, i.e. one with
nonvanishing discriminant — is modular. -/

def modularity : Prop := ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → IsModular W

/-! ## The curve `11a1` and its newform -/

/-- The elliptic curve `11a1 : y² + y = x³ - x² - 10x - 20`, of conductor `11`. -/
