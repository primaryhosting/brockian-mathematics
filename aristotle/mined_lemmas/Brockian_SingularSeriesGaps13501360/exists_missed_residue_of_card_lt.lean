/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) when for every prime `p` the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem exists_missed_residue_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : p.Prime)
    (h : H.card < p) : ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : (H.image (fun x : ℤ => (x : ZMod p))).card < Fintype.card (ZMod p) := by
    calc (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := h
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
  have hne : (H.image (fun x : ℤ => (x : ZMod p))) ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard
  rw [Ne, Finset.eq_univ_iff_forall] at hne
  push_neg at hne
  obtain ⟨r, hr⟩ := hne
  exact ⟨r, fun x hx hxr => hr (Finset.mem_image.mpr ⟨x, hx, hxr⟩)⟩

/-- An even integer reduces to `0` modulo `2`
(`ZMod.intCast_zmod_eq_zero_iff_dvd`). -/
