/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- A finite set of non-negative integers `H` is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture) if for every prime `p` the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently, the local factor of the
singular series `𝔖(H)` attached to `H` is non-zero at every prime. -/

theorem exists_missing_residue_of_card_lt {H : Finset ℕ} {p : ℕ} (hp : H.card < p) :
    ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  have hsub : H.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨h, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) hp))
  have hcard : (H.image (· % p)).card < (Finset.range p).card := by
    calc (H.image (· % p)).card ≤ H.card := Finset.card_image_le
    _ < p := hp
    _ = (Finset.range p).card := (Finset.card_range p).symm
  obtain ⟨r, hr, hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨r, Finset.mem_range.1 hr, ?_⟩
  intro h hh hmod
  exact hr' (Finset.mem_image.2 ⟨h, hh, hmod⟩)

/-- The `5`-tuple `{0, 2, 6, 8, 12}` is admissible: it is a prime constellation pattern of
diameter `12`. -/
