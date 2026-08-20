/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if for every prime `p` there is a residue
class mod `p` avoided by every element of `H`.  Equivalently, `H` does not cover all residues
modulo any prime; this is exactly the condition under which the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)/(1 - 1/p)^{|H|}` has no vanishing local factor. -/

theorem exists_missing_residue_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := h
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  have hex : ∃ r : ZMod p, r ∉ H.image (fun x : ℤ => (x : ZMod p)) := by
    by_contra hc
    push_neg at hc
    have huniv : (H.image (fun x : ℤ => (x : ZMod p))) = Finset.univ :=
      Finset.eq_univ_of_forall hc
    simp [huniv] at hcard
  obtain ⟨r, hr⟩ := hex
  exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- **Singular Series Gaps 13501360.**
For every integer `n`, the triple `{n, n + 1350, n + 1360}` is admissible: it avoids at least
one residue class modulo every prime.  Thus the gap range pattern `(1350, 1360)` extends the
family of admissible gap configurations, and the associated singular series has no vanishing
local factor. -/
