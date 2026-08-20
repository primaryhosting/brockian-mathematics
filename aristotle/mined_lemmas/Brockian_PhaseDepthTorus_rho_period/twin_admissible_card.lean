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

theorem twin_admissible_card (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : 2 < ℓ) :
    (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a)).card = ℓ - 2 := by
  classical
  have h_neg2_ne_0 : (-2 : ZMod ℓ) ≠ 0 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod ℓ) = 0 := by simpa using h
    rw [ZMod.natCast_eq_zero_iff] at h2
    linarith [Nat.le_of_dvd (by norm_num) h2]
  -- TwinAdmissibleAt ℓ a = (a ≠ 0 ∧ a + 2 ≠ 0) = (a ≠ 0 ∧ a ≠ -2)
  have h_equiv : ∀ a : ZMod ℓ, TwinAdmissibleAt ℓ a ↔ a ≠ 0 ∧ a ≠ -2 := by
    intro a
    simp [TwinAdmissibleAt]
    have : ¬(a + 2 = 0) ↔ a ≠ -2 := by
      constructor
      · intro ha2 hne
        apply ha2
        rw [hne]
        ring
      · intro ha_neg2 h
        apply ha_neg2
        have : a = -2 := by linear_combination h
        exact this
    tauto
  -- Rewrite using h_equiv
  have h_set_eq : (Finset.univ.filter (fun a : ZMod ℓ => TwinAdmissibleAt ℓ a)) =
      Finset.univ.filter (fun a : ZMod ℓ => a ≠ 0 ∧ a ≠ -2) := by
    congr 1
    ext a
    exact h_equiv a
  rw [h_set_eq]
  -- The set {a | a ≠ 0 ∧ a ≠ -2} is the complement of {0, -2}
  -- First, show {a | a ≠ 0 ∧ a ≠ -2} = Finset.univ \ {0, -2}
  have h_filter_eq_diff : Finset.univ.filter (fun a : ZMod ℓ => a ≠ 0 ∧ a ≠ -2) =
      Finset.univ \ {0, -2} := by
    ext a
    simp [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  rw [h_filter_eq_diff]
  -- Now compute the cardinality: |univ \ {0, -2}| = ℓ - 2
  have h_pair_eq : ({0, -2} : Finset (ZMod ℓ)) = {0, -2} := rfl
  have h_pair_card : ({0, -2} : Finset (ZMod ℓ)).card = 2 := by
    rw [Finset.card_pair]
    exact h_neg2_ne_0.symm
  rw [Finset.card_sdiff]
  simp [Finset.card_univ, h_pair_card, Finset.inter_univ]
  -- TARGET: complement is {0, -2}; card 2 since (-2 : ZMod ℓ) ≠ 0 for ℓ ∤ 2;
        -- then Finset.card_univ (ZMod ℓ) = ℓ and subtract.

/-- BM-GRAM-002 (twin primes obey the grammar): a twin start above ℓ is
    admissible at ℓ. -/
