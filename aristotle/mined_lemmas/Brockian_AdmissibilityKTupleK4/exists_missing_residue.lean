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
