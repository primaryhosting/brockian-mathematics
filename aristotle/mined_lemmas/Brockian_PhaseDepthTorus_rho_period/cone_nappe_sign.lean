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

theorem cone_nappe_sign (n : ℤ) (hn : n ≠ 0) :
    ((cone n).2.2 > 0 ↔ n > 0) ∧ ((cone n).2.2 < 0 ↔ n < 0) := by
  unfold cone
  have hs : (0:ℝ) < Real.sqrt 2 / 2 := by positivity
  constructor
  · constructor
    · intro h
      by_contra hle
      push_neg at hle
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hle
      nlinarith
    · intro h
      have : (0:ℝ) < (n : ℝ) := by exact_mod_cast h
      positivity
  · constructor
    · intro h
      by_contra hle
      push_neg at hle
      have : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      nlinarith
    · intro h
      have hn' : (n : ℝ) < 0 := by exact_mod_cast h
      have := mul_neg_of_neg_of_pos hn' hs
      simpa using this

/-! ## Phase–depth return (figure Act III; lineage BM-RET-001) -/

/-- The phase–depth state and its unit step. -/
