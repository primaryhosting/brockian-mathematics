import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem cond_of_davis (p q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y : ℕ)
    (h : ∀ k < y, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0) :
    ∃ (u K : ℕ) (a : Fin n → ℕ), davisCond p q v y u K a := by
  classical
  have hch : ∀ k : ℕ, ∃ t : Fin n → ℕ, k < y → p (Sum.elim (Option.elim' k v) t) = 0 := by
    intro k
    rcases lt_or_ge k y with hk | hk
    · obtain ⟨t, ht⟩ := h k hk; exact ⟨t, fun _ => ht⟩
    · exact ⟨fun _ => 0, fun hk' => absurd hk' (by omega)⟩
  choose tt htt using hch
  set tt' : ℕ → Fin n → ℕ := fun k i => if k < y then tt k i else 0 with htt'
  set u : ℕ := (Finset.range (y + 1)).sup (fun k => Finset.univ.sup (fun i => tt' k i)) with hu
  have hub : ∀ k ≤ y, ∀ i, tt' k i ≤ u := by
    intro k hk i
    refine le_trans (Finset.le_sup (f := fun i => tt' k i) (Finset.mem_univ i)) ?_
    exact Finset.le_sup (f := fun k => Finset.univ.sup (fun i => tt' k i))
      (Finset.mem_range.2 (by omega))
  refine ⟨u, ?_⟩
  set B := davisB q v y u with hB
  set b := davisb q v y u with hbdef
  have huB : u < B := lt_davisB q v y u
  have hyB : y ≤ B := by rw [hB, davisB]; omega
  have hBb : B ≤ b := davisB_le_davisb q v y u
  have hb1 : 0 < b := davisb_pos q v y u
  have hbfac : ∀ d, 0 < d → d ≤ y → d ∣ b := fun d hd hdy =>
    hbdef ▸ Nat.dvd_factorial hd (le_trans hdy hyB)
  have hyfac : (y)! ∣ b := hbdef ▸ Nat.factorial_dvd_factorial hyB
  have hklt : ∀ k : ℕ, k < 1 + (k + 1) * b := by
    intro k
    have : (k + 1) * 1 ≤ (k + 1) * b := Nat.mul_le_mul_left _ hb1
    omega
  have hmlt : ∀ k : ℕ, ∀ z ≤ u, z < 1 + (k + 1) * b := by
    intro k z hz
    have : b ≤ (k + 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨K, hK⟩ := exists_crt_code (fun k => k) y b hyfac (fun i _ => hklt i)
  have hai : ∀ i : Fin n, ∃ ai, ∀ k ≤ y, ai % (1 + (k + 1) * b) = tt' k i := fun i =>
    exists_crt_code (fun k => tt' k i) y b hyfac (fun k hk => hmlt k _ (hub k hk i))
  choose a ha using hai
  have hKmod : ∀ k ≤ y, K ≡ k [MOD 1 + (k + 1) * b] := by
    intro k hk
    show K % _ = k % _
    rw [hK k hk, Nat.mod_eq_of_lt (hklt k)]
  have hamod : ∀ (i : Fin n), ∀ k ≤ y, a i ≡ tt' k i [MOD 1 + (k + 1) * b] := by
    intro i k hk
    show a i % _ = tt' k i % _
    rw [ha i k hk, Nat.mod_eq_of_lt (hmlt k _ (hub k hk i))]
  refine ⟨K, a, ?_, ?_, ?_⟩
  · refine progProd_dvd_of_forall hbfac (fun k hk => ?_)
    have h1 : b * K + b + 1 ≡ b * k + b + 1 [MOD 1 + (k + 1) * b] :=
      (((hKmod k hk.le).mul_left b).add_right b).add_right 1
    have h2 : b * k + b + 1 = 1 + (k + 1) * b := by ring
    rw [h2] at h1
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  · intro i
    refine progProd_dvd_of_forall hbfac (fun k hk => ?_)
    exact dvd_descFactorial_of_modEq (hamod i k hk.le) (hub k hk.le i)
  · refine progProd_dvd_of_forall hbfac (fun k hk => ?_)
    have hcong : ∀ j : Option α ⊕ Fin n,
        ((Sum.elim (Option.elim' K v) a j : ℕ) : ℤ)
          ≡ ((Sum.elim (Option.elim' k v) (tt' k) j : ℕ) : ℤ)
            [ZMOD ((1 + (k + 1) * b : ℕ) : ℤ)] := by
      rintro (c | i)
      · rcases c with _ | c
        · exact (Int.natCast_modEq_iff (n := 1 + (k + 1) * b)).mpr (hKmod k hk.le)
        · exact Int.ModEq.refl _
      · exact (Int.natCast_modEq_iff (n := 1 + (k + 1) * b)).mpr (hamod i k hk.le)
    have hzero : p (Sum.elim (Option.elim' k v) (tt' k)) = 0 := by
      have he : tt' k = tt k := by funext i; simp [htt', hk]
      rw [he]
      exact htt k hk
    have hmod := poly_int_modEq p (1 + (k + 1) * b) _ _ hcong
    rw [hzero] at hmod
    have hdz : ((1 + (k + 1) * b : ℕ) : ℤ) ∣ p (Sum.elim (Option.elim' K v) a) :=
      Int.modEq_zero_iff_dvd.mp hmod
    have h4 := (Int.natAbs_dvd_natAbs (a := ((1 + (k + 1) * b : ℕ) : ℤ))).mpr hdz
    rwa [Int.natAbs_natCast] at h4

/-- **Davis' key equivalence.**  A bounded universal statement about a Diophantine condition is
equivalent to a purely existential statement. -/
