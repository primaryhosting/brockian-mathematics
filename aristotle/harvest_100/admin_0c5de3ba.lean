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
theorem exists_missing_residue (H : Finset ℤ) (p : ℕ) (hp : p.Prime)
    (hcard : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, ((h : ℤ) : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ H.image (fun h : ℤ => (h : ZMod p)) := by
    by_contra hcon
    push_neg at hcon
    have hsub : Finset.univ ⊆ H.image (fun h : ℤ => (h : ZMod p)) := fun x _ => hcon x
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    exact absurd hlt (not_lt.2 hle)
  exact ⟨r, fun h hh he => hr (Finset.mem_image.2 ⟨h, hh, he⟩)⟩

/-- **Admissibility of a prime `4`-tuple pattern.**  The tuple `(0, 2, 6, 8)` is admissible:
for every prime `p` some residue class mod `p` is omitted.  (For `p = 2` and `p = 3` the
class of `1` is omitted; for `p ≥ 5` this is pure pigeonhole since the tuple has only
`4` elements.) -/
theorem AdmissibilityKTupleK4 : IsAdmissible {0, 2, 6, 8} := by
  intro p hp
  rcases lt_or_ge p 5 with h5 | h5
  · interval_cases p
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact ⟨1, by intro h hh; fin_cases hh <;> decide⟩
    · exact ⟨1, by intro h hh; fin_cases hh <;> decide⟩
    · exact absurd hp (by decide)
  · refine exists_missing_residue _ p hp ?_
    have hc : ({0, 2, 6, 8} : Finset ℤ).card = 4 := by decide
    omega

end Brockian

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

