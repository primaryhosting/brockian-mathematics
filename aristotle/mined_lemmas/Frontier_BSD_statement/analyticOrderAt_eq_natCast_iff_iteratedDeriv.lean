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

set_option grind.warning false

namespace Frontier

/-!
## The arithmetic side: the Mordell–Weil rank

We work with an integral Weierstrass model `W : WeierstrassCurve ℤ` with nonzero
discriminant; the associated elliptic curve over `ℚ` is the base change
`W.map (Int.castRingHom ℚ)`, whose group of rational points is
`(W.map (Int.castRingHom ℚ)).toAffine.Point` (affine nonsingular points together with
the point at infinity).
-/

/-- The Mordell–Weil group `E(ℚ)` of the integral Weierstrass model `W`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the `ℚ`-dimension of `ℚ ⊗_ℤ E(ℚ)`
(equivalently, the rank of the free part of the finitely generated abelian group `E(ℚ)`). -/

theorem analyticOrderAt_eq_natCast_iff_iteratedDeriv {L : ℂ → ℂ} (hL : AnalyticAt ℂ L 1)
    (n : ℕ) :
    analyticOrderAt L 1 = (n : ℕ∞) ↔
      (∀ i < n, iteratedDeriv i L 1 = 0) ∧ iteratedDeriv n L 1 ≠ 0 := by
  have key := fun m : ℕ =>
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (f := L) (z₀ := 1) (n := m) hL
  constructor
  · intro h
    refine ⟨(key n).mp (le_of_eq h.symm), fun hn => ?_⟩
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt L 1 := by
      refine (key (n + 1)).mpr fun i hi => ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · exact (key n).mp (le_of_eq h.symm) i hi'
      · exact hn
    rw [h] at hle
    have : n + 1 ≤ n := by exact_mod_cast hle
    omega
  · rintro ⟨h1, h2⟩
    have hle : (n : ℕ∞) ≤ analyticOrderAt L 1 := (key n).mpr h1
    have hlt : analyticOrderAt L 1 < ((n + 1 : ℕ) : ℕ∞) :=
      not_le.mp fun hc => h2 ((key (n + 1)).mp hc n (Nat.lt_succ_self n))
    push_cast at hlt
    exact le_antisymm (Order.le_of_lt_add_one hlt) hle

/-- **The rank zero case.** For an entire `L`, BSD in rank `0` says exactly that
`L(E, 1) ≠ 0`. -/
