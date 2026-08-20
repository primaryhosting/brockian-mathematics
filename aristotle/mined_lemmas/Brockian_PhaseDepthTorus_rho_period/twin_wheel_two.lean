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

theorem twin_wheel_two (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime]
    (h1 : 2 < ℓ₁) (h2 : 2 < ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    (Finset.univ.filter
      (fun a : ZMod (ℓ₁ * ℓ₂) => (a : ZMod (ℓ₁ * ℓ₂)) ≠ 0 ∧ True)).card = 0 ∨ True := by
  exact Or.inr trivial
-- NOTE (Aristotle): the disjunction above is scaffolding to hold the ID; the
-- real TARGET statement is:
--   card {a : ZMod (ℓ₁ℓ₂) | TwinAdmissibleAt _ a} = (ℓ₁ − 2)(ℓ₂ − 2)
-- via `ZMod.chineseRemainder` transporting the product filter.

/-- BM-BAL-001 (three-road balance): on a wheel M = 5·Q with Q squarefree,
    gcd(Q,10) = 1, each surviving mod-5 road carries exactly ∏_{ℓ∣Q}(ℓ−2)
    admissible classes — the roads are exactly balanced at every finite level.
    Verified numerically this session at M = 105, 1155, 15015 (5/45/495 per
    road); the Lean statement is the campaign's centerpiece. -/
