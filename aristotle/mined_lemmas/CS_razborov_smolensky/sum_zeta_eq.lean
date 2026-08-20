import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem sum_zeta_eq {p : ℕ} (hp : 0 < p) {ζ : F} (hζp : ζ ^ p = 1) (w : ℕ) :
    ∑ a : Fin p, ζ ^ (p - (a : ℕ)) * (if (w + (a : ℕ)) % p = 0 then (1 : F) else 0) = ζ ^ w := by
  classical
  -- the unique `a₀ < p` with `p ∣ w + a₀`
  obtain ⟨a₀, ha₀lt, ha₀⟩ : ∃ a₀, a₀ < p ∧ p ∣ (w + a₀) := by
    rcases Nat.eq_zero_or_pos (w % p) with h | h
    · exact ⟨0, hp, by simpa using Nat.dvd_of_mod_eq_zero h⟩
    · refine ⟨p - w % p, by omega, ?_⟩
      have hw : w % p < p := Nat.mod_lt _ hp
      have h1 : w = p * (w / p) + w % p := (Nat.div_add_mod w p).symm
      refine ⟨w / p + 1, ?_⟩
      have : p * (w / p + 1) = p * (w / p) + p := by ring
      omega
  have huniq : ∀ a : ℕ, a < p → p ∣ (w + a) → a = a₀ := by
    intro a hal hdvd
    rcases le_total a a₀ with h | h
    · have : p ∣ (a₀ - a) := by
        have := Nat.dvd_sub ha₀ hdvd
        simpa [Nat.add_sub_add_left] using this
      have := Nat.eq_zero_of_dvd_of_lt this
      omega
    · have : p ∣ (a - a₀) := by
        have := Nat.dvd_sub hdvd ha₀
        simpa [Nat.add_sub_add_left] using this
      have := Nat.eq_zero_of_dvd_of_lt this
      omega
  have hkey := Finset.sum_eq_single (M := F) (s := (Finset.univ : Finset (Fin p))) (f := fun a : Fin p =>
      ζ ^ (p - (a : ℕ)) * (if (w + (a : ℕ)) % p = 0 then (1 : F) else 0))
    (⟨a₀, ha₀lt⟩ : Fin p) ?_ ?_
  · rw [hkey]
    simp only []
    rw [if_pos (Nat.dvd_iff_mod_eq_zero.mp ha₀), mul_one,
      zeta_pow_mod hζp (p - a₀), zeta_pow_mod hζp w]
    congr 1
    rcases Nat.eq_zero_or_pos a₀ with h0 | h0
    · subst h0
      have hw : p ∣ w := by simpa using ha₀
      rw [Nat.sub_zero, Nat.mod_self, Nat.dvd_iff_mod_eq_zero.mp hw]
    · obtain ⟨s, hs⟩ := ha₀
      have hs1 : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h | h
        · subst h; simp at hs; omega
        · exact h
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hps : p * (s' + 1) = p * s' + p := by ring
      have hw : w = p * s' + (p - a₀) := by omega
      rw [hw, Nat.mul_add_mod]
  · intro b _ hb
    refine mul_eq_zero_of_right _ (if_neg ?_)
    intro hcon
    exact hb (Fin.ext (huniq b b.2 (Nat.dvd_of_mod_eq_zero hcon)))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The final numerical contradiction -/

