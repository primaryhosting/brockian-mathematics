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

theorem tau_period (n : ℤ) : tau (n + 25) = tau n := by
  apply Prod.ext
  · change ((n + 25 - 1 : ℤ) : ZMod 5) = ((n - 1 : ℤ) : ZMod 5)
    push_cast
    change (n : ZMod 5) + (25 : ZMod 5) - 1 = (n : ZMod 5) - 1
    have h25 : (25 : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff 25 5).mpr (by norm_num)
    rw [h25]
    simp
  · change ((2 * (n + 25 - 1) : ℤ) : ZMod 25) =
      ((2 * (n - 1) : ℤ) : ZMod 25)
    push_cast
    change (2 : ZMod 25) * ((n : ZMod 25) + 25 - 1) =
      (2 : ZMod 25) * ((n : ZMod 25) - 1)
    have h25 : (25 : ZMod 25) = 0 := ZMod.natCast_self 25
    rw [h25]
    simp

/-- BM-TORUS-001b (no smaller positive period). -/
