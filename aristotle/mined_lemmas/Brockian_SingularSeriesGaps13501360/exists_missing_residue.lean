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

set_option grind.warning false

namespace Brockian

/-! # Admissible gap ranges and the Hardy–Littlewood singular series for prime pairs

For a gap `g` we consider the two–element pattern `{0, g}`.  Such a pattern is
*admissible* when, for every prime `p`, its residues do not cover all of `ZMod p`.
The Hardy–Littlewood singular series of the pattern `{0, g}` is
`𝔖(g) = 2 C₂ ∏_{p ∣ g, p odd} (p-1)/(p-2)` for even `g`, and `0` for odd `g`;
here we work with the arithmetic factor `∏_{p ∣ g, p odd} (p-1)/(p-2)` and with the
convention that the factor vanishes for odd `g` (matching the vanishing of `𝔖`).
-/

/-- A finite pattern `H ⊆ ℤ` is *admissible* if for every prime `p` some residue class
mod `p` is missed by `H`. -/

lemma exists_missing_residue (p : ℕ) (hp : p.Prime) (H : Finset ℤ) (hcard : H.card < p) :
    ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set S : Finset (ZMod p) := H.image (fun x : ℤ => (x : ZMod p)) with hS
  have h1 : S.card < Fintype.card (ZMod p) := by
    have h := Finset.card_image_le (s := H) (f := fun x : ℤ => (x : ZMod p))
    rw [← hS] at h
    rw [ZMod.card]
    omega
  have h2 : S ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ] at h1
    omega
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact h2 (Finset.eq_univ_iff_forall.mpr hcon)
  refine ⟨r, fun h hh hcontra => hr ?_⟩
  rw [hS, ← hcontra]
  exact Finset.mem_image_of_mem _ hh

/-- Even gaps give admissible pairs. -/
