/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring is repeated immediately after the imports.)

import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The arithmetic side: Mordell–Weil rank

An elliptic curve over `ℚ` is presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (a global minimal model, see `Frontier.IsGlobalMinimal`).  Its group of
rational points is the Mordell–Weil group `(W.map (Int.castRingHom ℚ)).toAffine.Point`, and its
rank is the dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve defined by the integral Weierstrass
model `W`. -/
abbrev RationalPoints (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The (algebraic) rank of `E(ℚ)`, defined as `dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.  For a finitely generated
abelian group this is the usual Mordell–Weil rank. -/

theorem HasseWeilData.L_unique {W : WeierstrassCurve ℤ} (D₁ D₂ : HasseWeilData W) :
    D₁.L = D₂.L := by
  have hcoeff : D₁.a = D₂.a := D₁.a_eq D₂
  -- The two `L`-functions agree on the half plane of absolute convergence.
  have hhalf : ∀ s : ℂ, 3 / 2 < s.re → D₁.L s = D₂.L s := by
    intro s hs
    have h₁ := D₁.L_hasSum s hs
    have h₂ := D₂.L_hasSum s hs
    rw [hcoeff] at h₁
    exact h₁.unique h₂
  -- The half plane is open, so they are eventually equal near `s = 2`.
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]
    norm_num
  have hev : D₁.L =ᶠ[nhds (2 : ℂ)] D₂.L :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) fun s hs => hhalf s hs
  -- Analytic continuation from a neighbourhood of `2` to all of `ℂ`.
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (f := D₁.L) (g := D₂.L) (U := Set.univ)
    (fun z _ => D₁.L_entire z) (fun z _ => D₂.L_entire z) isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) hev
  funext z
  exact this (Set.mem_univ z)

/-! ## The Birch and Swinnerton-Dyer statement -/

/-- **Birch–Swinnerton-Dyer**, formalized statement together with a Lean-checked reduction.

For every global minimal integral Weierstrass model `W` of an elliptic curve `E / ℚ`
(the hypotheses of minimality and nonsingularity being part of `Frontier.HasseWeilData`):

1. *Well-posedness.*  Any two Hasse–Weil data for `W` have the same `L`-function; hence the
   analytic rank `ord_{s=1} L(E, s)` is a genuine invariant of `E`.
2. *Reduction to a single `L`-function.*  BSD for `E`, i.e. `ord_{s=1} L(E, s) = rank E(ℚ)`,
   holds if and only if the equality holds for one (equivalently, any) choice of Hasse–Weil data.
3. *Base case (rank zero).*  If `E(ℚ)` is finite — so that `rank E(ℚ) = 0` — then BSD for `E`
   is equivalent to the non-vanishing `L(E, 1) ≠ 0`.

The full conjecture (that the equality in (2) always holds) remains open; what is proved here is
the formal statement, its well-posedness, and the rank-zero reduction. -/
