/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` the residues of the
elements of `H` do not cover all of `ZMod p`, i.e. some residue class mod `p` is missed. -/

theorem AdmissibilityKTupleK4 (H : Finset ℤ) (hcard : H.card = 4)
    (h2 : ∃ r : ZMod 2, ∀ h ∈ H, (h : ZMod 2) ≠ r)
    (h3 : ∃ r : ZMod 3, ∀ h ∈ H, (h : ZMod 3) ≠ r) :
    IsAdmissible H := by
  intro p hp
  rcases lt_or_ge p 5 with hlt | hge
  · interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact h2
    · exact h3
    · exact absurd hp (by norm_num)
  · exact exists_residue_not_hit hp (by omega)

/-- The classical prime quadruplet pattern `{0, 2, 6, 8}` is an admissible `4`-tuple. -/
