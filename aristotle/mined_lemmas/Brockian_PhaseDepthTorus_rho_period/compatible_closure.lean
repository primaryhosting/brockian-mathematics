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

theorem compatible_closure (L : ℤ) :
    (∀ n : ℤ, phi (n + L) = phi n) ↔ (5 : ℤ) ∣ L := by
  constructor
  · intro h
    have h1 := h 1
    unfold phi at h1
    have : ((L : ℤ) : ZMod 5) = 0 := by
      push_cast at h1 ⊢
      simpa using h1
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd L 5).mp this
  · intro hdvd n
    unfold phi
    obtain ⟨k, rfl⟩ := hdvd
    push_cast
    have h5 : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
    rw [h5]
    ring

/-! ## The discrete toroidal orbit (figure Act IV) -/

/-- The discrete torus state of n: tube phase in ZMod 5, hole class in ZMod 25
    (hole angle = 2·2π(n−1)/25 ⇒ hole class 2(n−1) mod 25). -/
