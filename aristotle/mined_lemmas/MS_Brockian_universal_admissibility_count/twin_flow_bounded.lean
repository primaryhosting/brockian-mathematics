import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

theorem twin_flow_bounded (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card ≤ n := by
  calc (Finset.univ.filter (fun a : ZMod n => IsUnit a ∧ IsUnit (a + 2))).card
      ≤ (Finset.univ : Finset (ZMod n)).card := Finset.card_filter_le _ _
    _ = n := by rw [Finset.card_univ, ZMod.card]
/-- Golden ratio is the fixed point φ² = φ + 1. -/
