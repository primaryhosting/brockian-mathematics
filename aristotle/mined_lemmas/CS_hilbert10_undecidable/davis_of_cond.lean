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

theorem davis_of_cond (p q : Poly (Option α ⊕ Fin n))
    (hq0 : ∀ w, 0 ≤ q w) (hqp : ∀ w, |p w| ≤ q w)
    (hqm : ∀ w w' : Option α ⊕ Fin n → ℕ, (∀ i, w i ≤ w' i) → q w ≤ q w')
    (v : α → ℕ) (y u K : ℕ) (a : Fin n → ℕ) (hC : davisCond p q v y u K a) :
    ∀ k < y, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0 := by
  obtain ⟨hC1, hC2, hC3⟩ := hC
  intro k hk
  set B := davisB q v y u with hB
  set b := davisb q v y u with hbdef
  have hb1 : 0 < b := davisb_pos q v y u
  have hBb : B ≤ b := davisB_le_davisb q v y u
  have huB : u < B := lt_davisB q v y u
  set m := 1 + (k + 1) * b with hm
  have hmP : m ∣ davisP q v y u := dvd_progProd hk
  have hm1 : m ≠ 1 := by
    have : b ≤ (k + 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨P, hPp, hPm⟩ := Nat.exists_prime_and_dvd hm1
  have hPPi : P ∣ davisP q v y u := hPm.trans hmP
  have hPb : ¬ P ∣ b := by
    intro hd
    have h1 : P ∣ (k + 1) * b := hd.mul_left _
    have h2 := Nat.dvd_sub hPm h1
    rw [hm] at h2
    simp at h2
    exact hPp.one_lt.ne' h2
  have hPB : B < P := by
    by_contra hcon
    push_neg at hcon
    exact hPb (hbdef ▸ Nat.dvd_factorial hPp.pos hcon)
  have huP : u < P := by omega
  -- `K` is congruent to `k` modulo `P`
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hPp
  have hd1 : (P : ℤ) ∣ (b : ℤ) * K + b + 1 := by
    have h := Int.natCast_dvd_natCast.mpr (hPPi.trans hC1)
    push_cast at h
    exact h
  have hd2 : (P : ℤ) ∣ (b : ℤ) * k + b + 1 := by
    have h : (P : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hPm
    rw [hm] at h
    push_cast at h
    have he : (1 : ℤ) + ((k : ℤ) + 1) * b = (b : ℤ) * k + b + 1 := by ring
    rwa [he] at h
  have hd4 : (P : ℤ) ∣ ((K : ℤ) - k) := by
    have hd3 : (P : ℤ) ∣ (b : ℤ) * ((K : ℤ) - k) := by
      have h := dvd_sub hd1 hd2
      have he : (b : ℤ) * K + b + 1 - ((b : ℤ) * k + b + 1) = (b : ℤ) * ((K : ℤ) - k) := by ring
      rwa [he] at h
    rcases hPz.dvd_mul.mp hd3 with h | h
    · exact absurd (Int.natCast_dvd_natCast.mp h) hPb
    · exact h
  have hKk : (K : ℤ) ≡ (k : ℤ) [ZMOD (P : ℤ)] := (Int.modEq_iff_dvd.mpr hd4).symm
  -- the residues of the witnesses modulo `P` are the required solution
  refine ⟨fun i => a i % P, ?_⟩
  set x : Fin n → ℕ := fun i => a i % P with hx
  have hxu : ∀ i, x i ≤ u := fun i =>
    mod_le_of_prime_dvd_descFactorial hPp huP (hPPi.trans (hC2 i))
  have hcong : ∀ i : Option α ⊕ Fin n,
      ((Sum.elim (Option.elim' k v) x i : ℕ) : ℤ) ≡ ((Sum.elim (Option.elim' K v) a i : ℕ) : ℤ)
        [ZMOD (P : ℤ)] := by
    rintro (c | i)
    · rcases c with _ | c
      · exact hKk.symm
      · exact Int.ModEq.refl _
    · simpa [hx] using (Int.natCast_modEq_iff (n := P)).mpr (Nat.mod_modEq (a i) P)
  have hpc : ((p (Sum.elim (Option.elim' k v) x) : ℤ)) ≡ p (Sum.elim (Option.elim' K v) a)
      [ZMOD (P : ℤ)] := poly_int_modEq p P _ _ hcong
  have hzero : (P : ℤ) ∣ p (Sum.elim (Option.elim' K v) a) := by
    have h := hPPi.trans hC3
    exact (Int.natAbs_dvd_natAbs (a := (P : ℤ))).mp (by simpa using h)
  have hdvd : (P : ℤ) ∣ p (Sum.elim (Option.elim' k v) x) :=
    Int.modEq_zero_iff_dvd.mp (hpc.trans (Int.modEq_zero_iff_dvd.mpr hzero))
  -- and the majorant shows that the value, being small and divisible by `P`, vanishes
  have hmaj : |p (Sum.elim (Option.elim' k v) x)|
      ≤ q (Sum.elim (Option.elim' y v) (fun _ => u)) := by
    refine (hqp _).trans (hqm _ _ ?_)
    rintro (c | i)
    · rcases c with _ | c
      · exact hk.le
      · exact le_refl _
    · exact hxu i
  have hnat : q (Sum.elim (Option.elim' y v) (fun _ => u))
      = ((q (Sum.elim (Option.elim' y v) (fun _ => u))).natAbs : ℤ) :=
    (Int.natAbs_of_nonneg (hq0 _)).symm
  have hle : (q (Sum.elim (Option.elim' y v) (fun _ => u))).natAbs ≤ B := by
    rw [hB]; simp [davisB]; omega
  by_contra hne
  have h1 := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have h2 : ((B : ℕ) : ℤ) < (P : ℤ) := by exact_mod_cast hPB
  have h3 : ((q (Sum.elim (Option.elim' y v) (fun _ => u))).natAbs : ℤ) ≤ (B : ℤ) := by
    exact_mod_cast hle
  rw [hnat] at hmaj
  omega

/-- The hard direction of Davis' equivalence: from solutions for every `k < y` one builds,
by Chinese remaindering, single numbers `K` and `a` coding them all. -/
