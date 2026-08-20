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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Filter Topology WeierstrassCurve

/-!
## Setup

An elliptic curve over `ℚ` is presented by an integral Weierstrass model `W : WeierstrassCurve ℤ`
with nonvanishing discriminant.  We formalize:

* the *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`;
* the local data (`a_p`, `ε_p`) and the Euler factors of the Hasse–Weil `L`-function of `W`;
* the predicate `IsHasseWeilLFunction W L` saying that the entire function `L` is the analytic
  continuation of the Hasse–Weil `L`-series of `W`;
* the Birch–Swinnerton-Dyer equality `ord_{s=1} L(E, s) = rank E(ℚ)`.
-/

/-- The Mordell–Weil group `E(ℚ)` of the Weierstrass model `W` over `ℤ`, namely the group of
nonsingular rational points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The *algebraic rank* of `W`, i.e. the rank of the Mordell–Weil group `E(ℚ)`, defined as the
dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

theorem lFunction_unique {W : WeierstrassCurve ℤ} {L₁ L₂ : ℂ → ℂ}
    (h₁ : IsHasseWeilLFunction W L₁) (h₂ : IsHasseWeilLFunction W L₂) : L₁ = L₂ := by
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : (2 : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.re_ofNat]
    norm_num
  have hev : L₁ =ᶠ[𝓝 (2 : ℂ)] L₂ :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem)
      (fun s hs => (h₁.euler s hs).trans (h₂.euler s hs).symm)
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => h₁.entire s) (fun s _ => h₂.entire s) hev

/-- Factorization form of the BSD equality: the order of vanishing of `L` at `s = 1` equals the
algebraic rank `r` exactly when `L(s) = (s-1)^r g(s)` near `s = 1` for some analytic `g` with
`g(1) ≠ 0`. -/
