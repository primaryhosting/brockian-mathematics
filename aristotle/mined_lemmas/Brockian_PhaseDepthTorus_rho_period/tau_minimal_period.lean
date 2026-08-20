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

theorem tau_minimal_period (d : ℕ) (hd : 0 < d)
    (h : ∀ n : ℤ, tau (n + d) = tau n) : 25 ≤ d := by
  have h2 : (2 : ZMod 25) * d = 0 := by
    have := h 1
    simp [tau] at this
    exact this.2
  have hdiv : (25 : ℤ) ∣ 2 * d := by
    have hdvd : 25 ∣ 2 * d := by
      have h2' : ((d * 2 : ℕ) : ZMod 25) = 0 := by rw [mul_comm] at h2; simp_all
      rw [show (2 : ℕ) * d = d * 2 by ring]
      have h2'' : ((d * 2 : ℕ) : ZMod 25) = 0 := h2'
      have := ZMod.natCast_eq_zero_iff (b := 25) (a := d * 2)
      exact_mod_cast this.mp h2''
    exact_mod_cast hdvd
  have hdiv_d : (25 : ℤ) ∣ d := Int.dvd_of_dvd_mul_right_of_gcd_one hdiv (by decide : Int.gcd 2 25 = 1)
  exact Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hdiv_d)
  -- TARGET: from the first component 5 ∣ d; from the second 25 ∣ 2d,
        -- and gcd(2,25) = 1 gives 25 ∣ d; combine with hd.

/-- BM-TORUS-002 (primitive winding, arithmetic form): the winding pair (5,2)
    is coprime, so the discrete orbit is a single cycle of length 25 in
    ZMod 5 × ZMod 25 — the arithmetic precursor of one-component-ness. -/
