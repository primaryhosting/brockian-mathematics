import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset


theorem card_dvd_le {m k q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin k)) (up : Fin k → Fin m)
    (hup : Function.Injective up) (w : Fin k → Bool) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (hw : w j₀ = true) :
    2 * (univ.filter (fun r : Fin m → Bool =>
        q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card)).card ≤ 2 ^ m := by
  set a := up j₀ with ha
  set flip : (Fin m → Bool) → (Fin m → Bool) :=
    fun r => fun c => if c = a then !(r c) else r c with hflip
  have hinv : Function.Involutive flip := by
    intro r; funext c; by_cases h : c = a <;> simp [hflip, h]
  set A := univ.filter (fun r : Fin m → Bool =>
      q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card) with hA
  have hkey : ∀ r : Fin m → Bool, ¬ (r ∈ A ∧ flip r ∈ A) := by
    rintro r ⟨h1, h2⟩
    simp only [hA, mem_filter, mem_univ, true_and] at h1 h2
    set T := S.filter (fun j => r (up j) = true ∧ w j = true) with hT
    set T' := S.filter (fun j => flip r (up j) = true ∧ w j = true) with hT'
    have hne : ∀ j : Fin k, j ≠ j₀ → flip r (up j) = r (up j) := by
      intro j hj
      have hja : up j ≠ a := fun hc => hj (hup hc)
      simp [hflip, hja]
    by_cases hb : r a = true
    · have hj₀T : j₀ ∈ T := by simp [hT, hj₀, hw, ← ha, hb]
      have hTT : T' = T.erase j₀ := by
        ext j
        simp only [hT, hT', mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hjS, hjr, hjw⟩
          have hj : j ≠ j₀ := by
            rintro rfl; rw [← ha] at hjr; simp [hflip, hb] at hjr
          exact ⟨hj, hjS, by rwa [hne j hj] at hjr, hjw⟩
        · rintro ⟨hj, hjS, hjr, hjw⟩
          exact ⟨hjS, by rwa [hne j hj], hjw⟩
      rw [hTT, Finset.card_erase_of_mem hj₀T] at h2
      have hc1 : 1 ≤ T.card := Finset.card_pos.2 ⟨j₀, hj₀T⟩
      have hd : q ∣ 1 := by
        have := Nat.dvd_sub h1 h2
        simpa [Nat.sub_sub_self hc1] using this
      have := Nat.le_of_dvd one_pos hd
      omega
    · have hb' : r a = false := by simpa using hb
      have hj₀T : j₀ ∉ T := by simp [hT, ← ha, hb']
      have hTT : T' = insert j₀ T := by
        ext j
        simp only [hT, hT', mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hjS, hjr, hjw⟩
          by_cases hj : j = j₀
          · exact Or.inl hj
          · exact Or.inr ⟨hjS, by rwa [hne j hj] at hjr, hjw⟩
        · rintro (rfl | ⟨hjS, hjr, hjw⟩)
          · exact ⟨hj₀, by rw [← ha]; simp [hflip, hb'], hw⟩
          · by_cases hj : j = j₀
            · subst hj; exact ⟨hjS, by rw [← ha]; simp [hflip, hb'], hjw⟩
            · exact ⟨hjS, by rwa [hne j hj], hjw⟩
      rw [hTT, Finset.card_insert_of_notMem hj₀T] at h2
      have hd : q ∣ 1 := by simpa using Nat.dvd_sub h2 h1
      have := Nat.le_of_dvd one_pos hd
      omega
  have hdisj : Disjoint A (A.image flip) := by
    rw [Finset.disjoint_right]
    rintro r hr hrA
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
    exact hkey s ⟨hs, hrA⟩
  have hcard : (A.image flip).card = A.card :=
    Finset.card_image_of_injective _ hinv.injective
  have hle : A.card + (A.image flip).card ≤ Fintype.card (Fin m → Bool) := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  rw [hcard] at hle
  simpa [Fintype.card_fun, two_mul] using hle

/-- The density of the set of randomness for which a single gate fails is at most `2^{-t}`. -/
