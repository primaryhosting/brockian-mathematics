import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Brockian

/-- A finite set `H` of integers is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) if for every prime `p` the reductions of the elements of `H`
modulo `p` fail to cover all residue classes, i.e. there is some residue `r : ZMod p`
omitted by `H`. -/

def IsAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, ((h : ℤ) : ZMod p) ≠ r

/-- Counting step: if `H` has fewer than `p` elements, then its reduction mod `p` cannot be
surjective, so some residue class is omitted.  This is a pigeonhole argument built from the
Mathlib lemmas `Finset.card_image_le`, `Finset.card_le_card` and `ZMod.card`. -/
