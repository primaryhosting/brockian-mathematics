/-
  Brockian/PhaseDepthTorus.lean — companion campaign module for
  "From the Signed Line to the Torus" (five-act figure, corrected edition).

  SUBMISSION NOTES (Aristotle):
  * Every claim ID below appears in the figure's companion ledger; the ledger's
    status badges are bound to this module's outcomes. Do not restate theorems.
  * CHARTER RULES (violations are returned, not audited):
    - No real-number `%` anywhere (ℝ is a field: a % b = 0). Residues live in
      ZMod; windings use explicit `∃ k : ℤ` terms.
    - Real exponents are written `((1:ℝ)/2)` or `Real.sqrt`, never `^(1/2)`.
    - No structure fields of bare type `Prop` outside named Conjecture containers.
    - Final proofs contain no unresolved tactic suggestions or unchecked evaluation.
    - A theorem may not wear a bigger theorem's name: nothing here claims
      knottedness of an embedded curve, and nothing here touches twin infinitude.
  * All target claims are kernel-checked; statements are kept unchanged.
-/
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Brockian.PhaseDepthTorus

/-! ## The two indexings, kept apart (figure: "ρ/φ dual indexing") -/

/-- Arithmetic residue ρ(n) = n mod 5, valued in ZMod 5.  Signed integers take
    their genuine classes: ρ(−1) = 4, ρ(−2) = 3, … -/

noncomputable def cone (n : ℤ) : ℝ × ℝ × ℝ :=
  ( (|n| : ℝ) * (Real.sqrt 2 / 2) * Real.cos (coneAngle n)
  , (|n| : ℝ) * (Real.sqrt 2 / 2) * Real.sin (coneAngle n)
  , (n : ℝ) * (Real.sqrt 2 / 2) )

/-- BM-CONE-001 (radial fidelity): the squared Euclidean norm of C(n) is n².
    Stated on squares to stay inside `nlinarith` territory; ‖C(n)‖ = |n| follows
    by `Real.sqrt_eq_iff` once this closes. -/
