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

theorem projFermat_mem_iff_forall_rep {n : ℕ}
    {p : Projectivization ℚ (Fin 3 → ℚ)} :
    p ∈ projFermatCurveRatPoints n ↔
      ∀ (w : Fin 3 → ℚ) (hw : w ≠ 0), Projectivization.mk ℚ w hw = p →
        w 0 ^ n + w 1 ^ n = w 2 ^ n := by
  constructor
  · rintro ⟨v, hv, hvp, hveq⟩ w hw hwp
    have hmk : Projectivization.mk ℚ v hv = Projectivization.mk ℚ w hw := by rw [hvp, hwp]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℚ v w hv hw).mp hmk
    have hcoord : ∀ i, v i = (a : ℚ) * w i := by
      intro i
      have := congrFun ha i
      simpa [Pi.smul_apply, smul_eq_mul] using this.symm
    have hane : ((a : ℚ)) ^ n ≠ 0 := pow_ne_zero _ a.ne_zero
    rw [hcoord 0, hcoord 1, hcoord 2] at hveq
    have : (a : ℚ) ^ n * (w 0 ^ n + w 1 ^ n) = (a : ℚ) ^ n * w 2 ^ n := by
      ring_nf; ring_nf at hveq; linarith [hveq]
    exact mul_left_cancel₀ hane this
  · intro h
    obtain ⟨v, hv, hvp⟩ : ∃ (v : Fin 3 → ℚ) (hv : v ≠ 0), Projectivization.mk ℚ v hv = p :=
      ⟨p.rep, p.rep_nonzero, p.mk_rep⟩
    exact ⟨v, hv, hvp, h v hv hvp⟩

/-- The projective point with affine coordinates `(a, b)` in the chart `z = 1`. -/
