/-
# Singular Series Gaps 14501460 — Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps14501460.lean`.  The target theorem there is
stated in plain core Lean (its file has to start with a fixed header comment, which forbids
`import`s).  Here the same mathematical content is formalized in the idiomatic Mathlib way,
with tuples as `Finset ℤ`, primality as `Nat.Prime`, and residues in `ZMod p`.
-/

import Mathlib

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the elements of `H` fail to cover
all residue classes modulo `p`.  Equivalently, the singular series attached to `H` is
nonzero. -/

theorem exists_missing_residue {p : ℕ} (hp : 0 < p) (H : Finset ℤ) (h : H.card < p) :
    ∃ r : ZMod p, ∀ a ∈ H, (a : ZMod p) ≠ r := by
  haveI : NeZero p := ⟨hp.ne'⟩
  by_contra hc
  push_neg at hc
  have himg : (H.image (fun a : ℤ => (a : ZMod p))) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro r
    obtain ⟨a, ha, hae⟩ := hc r
    exact Finset.mem_image.mpr ⟨a, ha, hae⟩
  have hcard := Finset.card_image_le (s := H) (f := fun a : ℤ => (a : ZMod p))
  rw [himg, Finset.card_univ, ZMod.card] at hcard
  omega

/-- The concrete four element tuple inside the gap range `[1450, 1460]`. -/
