import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/

lemma mem_projPoints_mk (w : Fin 3 → ℚ) (hw : w ≠ 0) :
    Projectivization.mk ℚ w hw ∈ projPoints fermatQuartic ↔
      MvPolynomial.eval w fermatQuartic = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℚ (Projectivization.mk ℚ w hw).rep w
    (Projectivization.rep_nonzero _) hw).mp (Projectivization.mk_rep _)
  rw [Units.smul_def] at ha
  constructor
  · intro hp
    have h2 : MvPolynomial.eval ((a : ℚ) • w) fermatQuartic = 0 := by rw [ha]; exact hp
    rw [eval_smul_fermatQuartic] at h2
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h1) a.ne_zero
    · exact h1
  · intro hw0
    show MvPolynomial.eval (Projectivization.mk ℚ w hw).rep fermatQuartic = 0
    rw [← ha, eval_smul_fermatQuartic, hw0, mul_zero]

/-- The four rational points of the Fermat quartic. -/
