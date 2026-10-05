import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: in Lean 4.28 the `import` command must be the very first command in a file, so the
required header docstring appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Setup

We work with an elliptic curve over `ℚ` presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (any elliptic curve over `ℚ` admits such a model).

* The *algebraic rank* is the rank of the Mordell–Weil group `E(ℚ)`, defined as the
  dimension of `ℚ ⊗_ℤ E(ℚ)` over `ℚ`.
* The *analytic rank* is the order of vanishing at `s = 1` of the Hasse–Weil `L`-function,
  where the `L`-function is specified by its Euler product on the half-plane of absolute
  convergence together with analytic continuation to `ℂ`.

Birch–Swinnerton-Dyer asserts that these two numbers agree.
-/

section Rank

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve given by the integral Weierstrass
model `W`, i.e. the group of rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The *algebraic rank* of `W`: the rank of the Mordell–Weil group `E(ℚ)`, defined as
`dim_ℚ (ℚ ⊗_ℤ E(ℚ))`. -/

theorem IsHasseWeilLFunction.unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) : L₁ = L₂ := by
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ := by
    filter_upwards [isOpen_halfPlane.mem_nhds hmem] with s hs
    exact (h₁.2 s hs).unique (h₂.2 s hs)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.1 s) (fun s _ => h₂.1 s) hev

/-- **Birch–Swinnerton-Dyer: statement and Lean-checked reduction.**

For every integral Weierstrass model `W` of an elliptic curve over `ℚ`:

1. (*Reduction*) BSD for `W` — the equality `ord_{s=1} L(E, s) = rank E(ℚ)` — is equivalent
   to the statement that every Hasse–Weil `L`-function `L` of `W` factors near `s = 1` as
   `L(s) = (s-1)^r g(s)` with `r = rank E(ℚ)` and `g` analytic at `1`, `g(1) ≠ 0`.
2. (*Base case*) If `rank E(ℚ) = 0`, BSD for `W` is equivalent to the nonvanishing
   `L(1) ≠ 0` of the Hasse–Weil `L`-function at the central point.
3. (*Single-`L` form*) Since the Hasse–Weil `L`-function is unique, BSD for `W` is
   equivalent to the equality `ord_{s=1} L = rank E(ℚ)` for any single `L` satisfying the
   specification. -/
