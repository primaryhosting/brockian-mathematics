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

theorem twin_start_admissible (ℓ p : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (hp : p.Prime) (hp2 : (p + 2).Prime) (h : ℓ < p) :
    TwinAdmissibleAt ℓ (p : ZMod ℓ) := by
  constructor
  · intro h0
    have : ℓ ∣ p := (ZMod.natCast_eq_zero_iff p ℓ).mp h0
    have := (Nat.Prime.eq_one_or_self_of_dvd hp ℓ this).resolve_left hℓ.one_lt.ne'
    omega
  · intro h0
    have h0' : ((p + 2 : ℕ) : ZMod ℓ) = 0 := by push_cast; simpa using h0
    have : ℓ ∣ p + 2 := (ZMod.natCast_eq_zero_iff (p+2) ℓ).mp h0'
    have := (Nat.Prime.eq_one_or_self_of_dvd hp2 ℓ this).resolve_left hℓ.one_lt.ne'
    omega

/-- BM-WHEEL-001 (twin-wheel counting): for squarefree odd M the admissible
    count is multiplicative — ∏_{ℓ ∣ M} (ℓ − 2) — via CRT.  Stated for a
    two-prime wheel first; the general form is the campaign target. -/
