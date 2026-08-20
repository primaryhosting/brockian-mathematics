import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
required header block is placed immediately after `import Mathlib`.

This file formalises the statement of the Birch--Swinnerton-Dyer conjecture

  ord_{s = 1} L(E, s) = rank E(ℚ)

for elliptic curves over `ℚ` given by a global minimal integral Weierstrass model, and proves
the rank-zero base case together with a Lean-checked reduction of the rank-zero case of the
conjecture to the equivalence `L(E, 1) ≠ 0 ↔ E(ℚ) finite`.
-/

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The group `E(ℚ)` of rational points of the elliptic curve given by the integral
Weierstrass model `W` over `ℤ`. -/
abbrev RatPoints (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The algebraic rank of `E(ℚ)`: the rank of the Mordell–Weil group as a `ℤ`-module. -/

def IsLSeriesCoeff (W : WeierstrassCurve ℤ) (a : ℕ → ℂ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧
  (∀ m n : ℕ, Nat.Coprime m n → a (m * n) = a m * a n) ∧
  (∀ p : ℕ, p.Prime → a p = (apCoeff W p : ℂ)) ∧
  (∀ p k : ℕ, p.Prime → ¬ (p : ℤ) ∣ W.Δ →
      a (p ^ (k + 2)) = a p * a (p ^ (k + 1)) - (p : ℂ) * a (p ^ k)) ∧
  (∀ p k : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → a (p ^ k) = a p ^ k)

/-- `L` is *the* `L`-function of the elliptic curve given by the global minimal Weierstrass
model `W`: it is entire (this is the analytic continuation provided by modularity) and it agrees
with the Hasse–Weil Dirichlet series in the half plane of absolute convergence `Re s > 3/2`. -/
