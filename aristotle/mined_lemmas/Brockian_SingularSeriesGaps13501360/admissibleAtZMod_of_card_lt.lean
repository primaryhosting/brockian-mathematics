import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/

theorem admissibleAtZMod_of_card_lt {H : Finset ℤ} {p : ℕ} (hp : 0 < p) (hcard : H.card < p) :
    AdmissibleAtZMod H p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have hlt : (H.image (fun h : ℤ => (h : ZMod p))).card < Finset.univ.card (α := ZMod p) := by
    have h1 : (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
    have h2 : Finset.univ.card (α := ZMod p) = p := by simp [ZMod.card]
    omega
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨r, fun h hh hcon => hr (Finset.mem_image.2 ⟨h, hh, hcon⟩)⟩

