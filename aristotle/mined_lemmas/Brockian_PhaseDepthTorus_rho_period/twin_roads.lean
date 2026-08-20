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

theorem twin_roads :
    (fun r => (r, r + 2)) '' {r : ZMod 5 | twinAdmissible r}
      = {((1:ZMod 5), (3:ZMod 5)), (2, 4), (4, 1)} := by
  rw [twin_survivors]
  ext p
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with rfl | rfl | rfl <;> simp <;> decide
  · rintro (rfl | rfl | rfl)
    · exact ⟨1, by simp, by decide⟩
    · exact ⟨2, by simp, by decide⟩
    · exact ⟨4, by simp, by decide⟩

/-! ## The general grammar and the wheel (Brockian Local Twin-Grammar program) -/

/-- Local twin-start admissibility at an arbitrary modulus. -/
