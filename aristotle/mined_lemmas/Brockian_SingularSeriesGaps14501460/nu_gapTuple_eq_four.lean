import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Brockian

/-- The gap window: the integers of the range `[1450, 1460]`. -/

lemma nu_gapTuple_eq_four {p : ℕ} (hp : 9 ≤ p) : nu gapTuple p = 4 := by
  have hinj : Set.InjOn (fun h : ℤ => (h : ZMod p)) gapTuple := by
    intro a ha b hb hab
    simp only at hab
    by_contra hne
    have hba := gapTuple_bounds b (Finset.mem_coe.mp hb)
    have haa := gapTuple_bounds a (Finset.mem_coe.mp ha)
    have hd : (p : ℤ) ∣ (b - a) := Int.ModEq.dvd ((ZMod.intCast_eq_intCast_iff a b p).mp hab)
    have hne' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hle : (p : ℤ) ≤ |b - a| := Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs _ _).mpr hd)
    have hp' : (9 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    rcases abs_cases (b - a) with ⟨he, -⟩ | ⟨he, -⟩ <;> omega
  simp only [nu]
  rw [Finset.card_image_of_injOn hinj, gapTuple_card]

