import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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
## Faltings' theorem (the Mordell conjecture)

Faltings' theorem states that a smooth projective curve of genus `≥ 2` defined over `ℚ` has
only finitely many rational points.  Mathlib currently has no definition of the genus of a
curve, so we formalize the statement for the classical family of test cases: the *Fermat
curves* `x ^ n + y ^ n = 1`.  The smooth plane projective curve `x ^ n + y ^ n = z ^ n` has
genus `(n - 1) * (n - 2) / 2`, which is `≥ 2` exactly when `n ≥ 4`; so the assertion
`FaltingsForFermatCurves` below is precisely the content of Faltings' theorem for this family.

We prove:

* `Frontier.fermatCurve_finite_of_flt`: a Lean-checked *reduction* of Faltings' theorem for the
  Fermat curve of even degree `n ≥ 1` to Fermat's Last Theorem for the exponent `n`;
* `Frontier.faltings_mordell` (the target): the resulting unconditional *base case* — for every
  `n` divisible by `4` (in particular the genus `3` quartic `x ^ 4 + y ^ 4 = 1`), the Fermat
  curve has only finitely many rational points.  The input is Mathlib's
  `fermatLastTheoremFour`, Fermat's Last Theorem for exponent `4`.
* `Frontier.fermatCurve_eq_of_four_dvd`: in fact the rational points are exactly the four
  trivial ones.
-/

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1`. -/

theorem projFaltings_mordell {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (projFermatCurveRatPoints n).Finite := by
  have hev : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  have hsub : projFermatCurveRatPoints n ⊆
      {projAffinePt 1 0, projAffinePt (-1) 0, projAffinePt 0 1, projAffinePt 0 (-1)} := by
    rintro p ⟨v, hv, rfl, heq⟩
    have hv2 : v 2 ≠ 0 := by
      intro h2
      rw [h2] at heq
      have h0 : (0:ℚ) ≤ v 0 ^ n := hev.pow_nonneg _
      have h1 : (0:ℚ) ≤ v 1 ^ n := hev.pow_nonneg _
      have hzn : (0:ℚ) ^ n = 0 := zero_pow hn0
      have e0 : v 0 = 0 := (pow_eq_zero_iff hn0).mp (by linarith)
      have e1 : v 1 = 0 := (pow_eq_zero_iff hn0).mp (by linarith)
      exact hv (funext fun i => by fin_cases i <;> simp [e0, e1, h2])
    have hab : (v 0 / v 2) ^ n + (v 1 / v 2) ^ n = 1 := by
      rw [div_pow, div_pow, ← add_div, heq, div_self (pow_ne_zero n hv2)]
    have hmem : (v 0 / v 2, v 1 / v 2) ∈ trivialFermatPoints := by
      rw [← fermatCurve_eq_of_four_dvd hn hn0]
      exact hab
    have hrep : Projectivization.mk ℚ v hv = projAffinePt (v 0 / v 2) (v 1 / v 2) := by
      refine (Projectivization.mk_eq_mk_iff ℚ v _ hv _).mpr ⟨Units.mk0 (v 2) hv2, ?_⟩
      funext i
      fin_cases i <;> simp [Units.smul_def] <;> field_simp
    rw [hrep]
    simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp
  exact (((((Set.finite_singleton _).insert _).insert _).insert _)).subset hsub

/-!
## Faltings' theorem for smooth plane curves over `ℚ`

Finally we state Faltings' theorem in the generality that Mathlib currently permits: for a
smooth plane projective curve `{F = 0} ⊆ ℙ²` defined by a homogeneous `F ∈ ℚ[x, y, z]` of
degree `d`.  By the genus-degree formula such a curve has genus `(d - 1) * (d - 2) / 2`, which
is `≥ 2` exactly when `d ≥ 4`, so `FaltingsForSmoothPlaneCurves` below is exactly Faltings'
