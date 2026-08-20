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
def davisB (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : ℕ :=
  (q (Sum.elim (Option.elim' y v) (fun _ => u))).natAbs + y + u + 1

/-- The modulus base `b = B !`. -/
def davisb (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : ℕ := (davisB q v y u)!

/-- The product of the moduli `1 + (k+1) * b` for `k < y`. -/
def davisP (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : ℕ :=
  progProd y (davisb q v y u)

/-- The three divisibility conditions of Davis' construction. -/
def davisCond (p q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u K : ℕ) (a : Fin n → ℕ) : Prop :=
  davisP q v y u ∣ davisb q v y u * K + davisb q v y u + 1 ∧
    (∀ i, davisP q v y u ∣ (a i).descFactorial (u + 1)) ∧
    davisP q v y u ∣ (p (Sum.elim (Option.elim' K v) a)).natAbs

theorem davisB_pos (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : 0 < davisB q v y u := by
  simp [davisB]

theorem lt_davisB (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : u < davisB q v y u := by
  simp [davisB]

theorem davisb_pos (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) : 0 < davisb q v y u :=
  Nat.factorial_pos _

theorem davisB_le_davisb (q : Poly (Option α ⊕ Fin n)) (v : α → ℕ) (y u : ℕ) :
    davisB q v y u ≤ davisb q v y u := Nat.self_le_factorial _

/-- The easy direction of Davis' equivalence: the three divisibility conditions force the
polynomial to vanish at every `k < y`. -/
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
theorem davis_iff (p q : Poly (Option α ⊕ Fin n))
    (hq0 : ∀ w, 0 ≤ q w) (hqp : ∀ w, |p w| ≤ q w)
    (hqm : ∀ w w' : Option α ⊕ Fin n → ℕ, (∀ i, w i ≤ w' i) → q w ≤ q w')
    (v : α → ℕ) (y : ℕ) :
    (∀ k < y, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0) ↔
      ∃ (u K : ℕ) (a : Fin n → ℕ), davisCond p q v y u K a :=
  ⟨cond_of_davis p q v y, fun ⟨_, _, _, hC⟩ => davis_of_cond p q hq0 hqp hqm v y _ _ _ hC⟩

/-! ### Bounded universal quantification is Diophantine -/

/-- Index type for the extra variables of Davis' construction: the three scalars `y`, `u`, `K`
followed by the `n` witness variables. -/
abbrev davisIdx (n : ℕ) : Type := Option (Option (Option (Fin n)))

/-- **Bounded universal quantification** preserves Diophantine sets. -/
theorem forall_lt_dioph {S : Set (Option α → ℕ)} {f : (α → ℕ) → ℕ}
    (d : Dioph S) (df : DiophFn f) :
    Dioph {v : α → ℕ | ∀ x < f v, Option.elim' x v ∈ S} := by
  classical
  obtain ⟨n, p, hp⟩ := dioph_fin d
  obtain ⟨q, hq0, hqp, hqm⟩ := exists_majorant p
  set sg : Option α ⊕ Fin n → α ⊕ davisIdx n :=
    Sum.elim (Option.elim' (Sum.inr none) Sum.inl) (fun _ => Sum.inr (some none)) with hsg
  set tu : Option α ⊕ Fin n → α ⊕ davisIdx n :=
    Sum.elim (Option.elim' (Sum.inr (some (some none))) Sum.inl)
      (fun i => Sum.inr (some (some (some i)))) with htu
  -- the basic Diophantine functions of the extended variable vector
  have dY : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr none)) :=
    Dioph.proj_dioph _
  have dU : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some none))) :=
    Dioph.proj_dioph _
  have dK : DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some (some none)))) :=
    Dioph.proj_dioph _
  have dA : ∀ i : Fin n,
      DiophFn (fun w : α ⊕ davisIdx n → ℕ => w (Sum.inr (some (some (some i))))) :=
    fun i => Dioph.proj_dioph _
  have dF : DiophFn (fun w : α ⊕ davisIdx n → ℕ => f (fun a => w (Sum.inl a))) :=
    Dioph.reindex_diophFn Sum.inl df
  -- the bound `B`, the modulus base `b` and the product of moduli are Diophantine
  have hqmap : ∀ w : α ⊕ davisIdx n → ℕ,
      (q.map sg) w = q (Sum.elim (Option.elim' (w (Sum.inr none)) (fun a => w (Sum.inl a)))
        (fun _ => w (Sum.inr (some none)))) := by
    intro w
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with (c | i)
    · rcases c with _ | c <;> rfl
    · rfl
  have dB : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisB q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) := by
    have h1 : DiophFn (fun w : α ⊕ davisIdx n → ℕ => ((q.map sg) w).natAbs) :=
      Dioph.abs_poly_dioph _
    have heq : (fun w : α ⊕ davisIdx n → ℕ =>
        davisB q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))))
        = fun w => ((q.map sg) w).natAbs + w (Sum.inr none)
            + w (Sum.inr (some none)) + 1 := by
      funext w
      rw [davisB, hqmap w]
    rw [heq]
    exact Dioph.add_dioph (Dioph.add_dioph (Dioph.add_dioph h1 dY) dU) (Dioph.const_dioph 1)
  have db : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) :=
    factorial_dioph dB
  have dP : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))) :=
    progProd_dioph dY db (fun w => davisb_pos _ _ _ _)
  -- the three divisibility conditions are Diophantine
  have dC1 : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
          * w (Sum.inr (some (some none)))
        + davisb q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
        + 1} :=
    Dioph.dvd_dioph dP (Dioph.add_dioph (Dioph.add_dioph (Dioph.mul_dioph db dK) db)
      (Dioph.const_dioph 1))
  have dC2 : Dioph {w : α ⊕ davisIdx n → ℕ | ∀ i : Fin n,
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1)} := by
    refine dioph_forall_fin n _ (fun i => ?_)
    have hd : DiophFn (fun w : α ⊕ davisIdx n → ℕ =>
        (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1)) := by
      have heq : (fun w : α ⊕ davisIdx n → ℕ =>
          (w (Sum.inr (some (some (some i))))).descFactorial (w (Sum.inr (some none)) + 1))
          = fun w => (w (Sum.inr (some none)) + 1)! *
              (w (Sum.inr (some (some (some i))))).choose (w (Sum.inr (some none)) + 1) := by
        funext w
        exact Nat.descFactorial_eq_factorial_mul_choose _ _
      rw [heq]
      exact Dioph.mul_dioph (factorial_dioph (Dioph.add_dioph dU (Dioph.const_dioph 1)))
        (choose_dioph (dA i) (Dioph.add_dioph dU (Dioph.const_dioph 1)))
    exact Dioph.dvd_dioph dP hd
  have hpmap : ∀ w : α ⊕ davisIdx n → ℕ,
      (p.map tu) w
        = p (Sum.elim (Option.elim' (w (Sum.inr (some (some none)))) (fun a => w (Sum.inl a)))
          (fun i => w (Sum.inr (some (some (some i)))))) := by
    intro w
    rw [Poly.map_apply]
    congr 1
    funext x
    rcases x with (c | i)
    · rcases c with _ | c <;> simp [htu]
    · simp [htu]
  have dC3 : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisP q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none))) ∣
        (p (Sum.elim (Option.elim' (w (Sum.inr (some (some none)))) (fun a => w (Sum.inl a)))
          (fun i => w (Sum.inr (some (some (some i))))))).natAbs} := by
    have h1 : DiophFn (fun w : α ⊕ davisIdx n → ℕ => ((p.map tu) w).natAbs) :=
      Dioph.abs_poly_dioph _
    have heq : (fun w : α ⊕ davisIdx n → ℕ => ((p.map tu) w).natAbs)
        = fun w =>
            (p (Sum.elim (Option.elim' (w (Sum.inr (some (some none))))
              (fun a => w (Sum.inl a))) (fun i => w (Sum.inr (some (some (some i))))))).natAbs := by
      funext w; rw [hpmap w]
    rw [heq] at h1
    exact Dioph.dvd_dioph dP h1
  have dCond : Dioph {w : α ⊕ davisIdx n → ℕ |
      davisCond p q (fun a => w (Sum.inl a)) (w (Sum.inr none)) (w (Sum.inr (some none)))
        (w (Sum.inr (some (some none)))) (fun i => w (Sum.inr (some (some (some i)))))} :=
    Dioph.ext ((dC1.inter dC2).inter dC3) (fun w => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, davisCond]
      tauto)
  have dC0 : Dioph {w : α ⊕ davisIdx n → ℕ |
      w (Sum.inr none) = f (fun a => w (Sum.inl a))} := Dioph.eq_dioph dY dF
  -- assemble
  refine Dioph.ext (Dioph.ex_dioph (dC0.inter dCond)) fun v => ?_
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨x, hC0, hCond⟩
    have hy : x none = f v := hC0
    intro k hk
    refine (hp _).2 (davis_of_cond p q hq0 hqp hqm v (x none) _ _ _ hCond k ?_)
    rw [hy]; exact hk
  · intro h
    have h' : ∀ k < f v, ∃ t : Fin n → ℕ, p (Sum.elim (Option.elim' k v) t) = 0 :=
      fun k hk => (hp _).1 (h k hk)
    obtain ⟨u, K, a, hCond⟩ := cond_of_davis p q v (f v) h'
    exact ⟨Option.elim' (f v) (Option.elim' u (Option.elim' K a)), rfl, hCond⟩

end CS

import RequestProject.MRDP

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Sum Nat MvPolynomial

namespace CS

/-! ### An undecidable recursively enumerable predicate on `ℕ` -/

/-- The halting problem transported to `ℕ` along the standard enumeration of codes. -/
def Halts (n : ℕ) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code n) 0).Dom

theorem halts_re : REPred Halts :=
  (ComputablePred.halting_problem_re 0).comp (Computable.ofNat Nat.Partrec.Code)

theorem halts_not_computable : ¬ ComputablePred Halts := by
  intro h
  refine ComputablePred.halting_problem 0 ?_
  obtain ⟨inst, hc⟩ := h
  refine ComputablePred.of_eq (p := fun c : Nat.Partrec.Code => Halts (Encodable.encode c))
    ⟨fun c => inst (Encodable.encode c), hc.comp Computable.encode⟩ ?_
  intro c
  simp [Halts]

/-! ### From `Poly` to `MvPolynomial` -/

/-- Every integer-valued multivariate polynomial function in the sense of `IsPoly` is the
evaluation of an honest `MvPolynomial` over `ℤ`. -/
theorem exists_mvPolynomial {γ : Type} : ∀ {f : (γ → ℕ) → ℤ}, IsPoly f →
    ∃ q : MvPolynomial γ ℤ, ∀ v : γ → ℕ, f v = MvPolynomial.eval (fun i => (v i : ℤ)) q := by
  intro f hf
  induction hf with
  | proj i => exact ⟨X i, by intro v; simp⟩
  | const n => exact ⟨C n, by intro v; simp⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, h1⟩ := ih1; obtain ⟨q2, h2⟩ := ih2
      exact ⟨q1 - q2, by intro v; simp [h1, h2]⟩
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, h1⟩ := ih1; obtain ⟨q2, h2⟩ := ih2
      exact ⟨q1 * q2, by intro v; simp [h1, h2]⟩

/-- A Diophantine predicate of one variable is given by an explicit integer polynomial with a
parameter: `p a` holds iff `P (a, x₁, …, xₙ) = 0` has a solution in natural numbers. -/
theorem exists_poly_of_dioph (p : ℕ → Prop) (hd : Dioph {v : Fin2 1 → ℕ | p (v Fin2.fz)}) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ), ∀ a : ℕ,
      (∃ x : Fin n → ℕ, MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) P = 0) ↔ p a := by
  classical
  obtain ⟨β, P, hP⟩ := hd
  obtain ⟨q, hq⟩ := exists_mvPolynomial P.isPoly
  obtain ⟨n, f, hfinj, q₀, rfl⟩ := MvPolynomial.exists_fin_rename q
  refine ⟨n, rename (fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i)) q₀, ?_⟩
  intro a
  have key : ∀ w : Fin n → ℕ, ∀ g : Fin2 1 ⊕ β → ℕ, (∀ i, g (f i) = w i) →
      (MvPolynomial.eval (fun i => (w i : ℤ)) q₀ = P g) := by
    intro w g hg
    rw [hq g, eval_rename]
    have : (fun i => ((w i : ℤ))) = ((fun i => (g i : ℤ)) ∘ f) := by
      funext i; simp [Function.comp, hg i]
    rw [this]
  have key2 : ∀ x : Fin n → ℕ,
      MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ))
        (rename (fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i)) q₀)
      = MvPolynomial.eval (fun i => ((Sum.elim (fun _ => a) (fun _ => x i) (f i) : ℕ) : ℤ)) q₀ := by
    intro x
    rw [eval_rename]
    have : ((Fin.cons (a : ℤ) fun i => (x i : ℤ)) ∘
        fun i => Sum.elim (fun _ => (0 : Fin (n + 1))) (fun _ => i.succ) (f i))
        = fun i => ((Sum.elim (fun _ => a) (fun _ => x i) (f i) : ℕ) : ℤ) := by
      funext i
      rcases h : f i with j | b <;> simp [Function.comp, h]
    rw [this]
  constructor
  · rintro ⟨x, hx⟩
    rw [key2] at hx
    refine (hP (fun _ => a)).2 ?_
    refine ⟨fun b => if h : ∃ i, f i = inr b then x h.choose else 0, ?_⟩
    rw [← key (fun i => Sum.elim (fun _ => a) (fun _ => x i) (f i)) _ ?_]
    · exact hx
    · intro i
      rcases h : f i with j | b
      · simp [h]
      · have hex : ∃ i', f i' = inr b := ⟨i, h⟩
        have hspec := hex.choose_spec
        have : hex.choose = i := hfinj (by rw [hspec, h])
        simp [h, hex, this]
  · intro hpa
    obtain ⟨t, ht⟩ := (hP (fun _ => a)).1 hpa
    refine ⟨fun i => Sum.elim (fun _ => 0) (fun b => t b) (f i), ?_⟩
    rw [key2, key _ (Sum.elim (fun _ => a) t) ?_]
    · exact ht
    · intro i; rcases h : f i with j | b <;> simp

/-! ### Hilbert's tenth problem -/

/-- **Hilbert's tenth problem is undecidable.**  There is a polynomial `P` with integer
coefficients in variables `x₀, x₁, …, xₙ` such that no algorithm decides, for a given natural
number `a`, whether the Diophantine equation `P (a, x₁, …, xₙ) = 0` is solvable. -/
theorem hilbert10_undecidable :
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ => ∃ x : Fin n → ℕ,
          MvPolynomial.eval (Fin.cons (a : ℤ) fun i => (x i : ℤ)) P = 0 := by
  obtain ⟨n, P, hP⟩ := exists_poly_of_dioph Halts (dioph_of_rePred Halts halts_re)
  refine ⟨n, P, fun h => halts_not_computable (ComputablePred.of_eq h ?_)⟩
  intro a
  exact hP a

/-! ### Solutions in the integers -/

/-- The substitution replacing each unknown by a sum of four squares of new unknowns, and
leaving the parameter untouched. -/
noncomputable def fourSq {m : ℕ} : Fin (m + 1) → MvPolynomial (Fin (m * 4 + 1)) ℤ :=
  Fin.cases (X 0) (fun i => ∑ k : Fin 4, (X (Fin.succ (finProdFinEquiv (i, k)))) ^ 2)

theorem eval_bind_fourSq {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) (a : ℤ)
    (y : Fin (m * 4) → ℤ) :
    eval (Fin.cons a y) (bind₁ fourSq P)
      = eval (Fin.cons a (fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2)) P := by
  rw [show eval (Fin.cons a y) (bind₁ fourSq P)
      = eval (fun i => eval (Fin.cons a y) (fourSq i)) P from
    MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℤ) (Fin.cons a y) fourSq P]
  have hfun : (fun i => eval (Fin.cons a y) (fourSq i))
      = Fin.cons a (fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [fourSq]
    · intro j
      simp [fourSq]
  rw [hfun]

/-- **Lagrange's trick.**  Solvability in natural numbers is equivalent to solvability in
integers once each unknown is replaced by a sum of four squares. -/
theorem exists_int_iff_exists_nat {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) (a : ℤ) :
    (∃ y : Fin (m * 4) → ℤ, eval (Fin.cons a y) (bind₁ fourSq P) = 0) ↔
      ∃ x : Fin m → ℕ, eval (Fin.cons a fun i => (x i : ℤ)) P = 0 := by
  classical
  constructor
  · rintro ⟨y, hy⟩
    rw [eval_bind_fourSq] at hy
    refine ⟨fun i => (∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat, ?_⟩
    have hcast : ∀ i : Fin m,
        (((∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat : ℤ))
          = ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2 := fun i =>
      Int.toNat_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
    rw [show (fun i : Fin m => (((∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat : ℤ)))
        = fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2 from funext hcast]
    exact hy
  · rintro ⟨x, hx⟩
    choose A B C D hABCD using fun i : Fin m => Nat.sum_four_squares (x i)
    refine ⟨fun j => ((![A ((finProdFinEquiv.symm j).1), B ((finProdFinEquiv.symm j).1),
      C ((finProdFinEquiv.symm j).1), D ((finProdFinEquiv.symm j).1)]
        ((finProdFinEquiv.symm j).2) : ℕ) : ℤ), ?_⟩
    rw [eval_bind_fourSq]
    have hsum : ∀ i : Fin m,
        (∑ k : Fin 4, (((![A i, B i, C i, D i] k : ℕ) : ℤ)) ^ 2) = (x i : ℤ) := by
      intro i
      rw [Fin.sum_univ_four]
      have h := hABCD i
      push_cast [← h]
      ring
    rw [show (fun i : Fin m => ∑ k : Fin 4,
        (((![A ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            B ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            C ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            D ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1)]
          ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).2) : ℕ) : ℤ)) ^ 2)
        = fun i : Fin m => (x i : ℤ) from funext (fun i => by
          simp only [Equiv.symm_apply_apply]
          exact hsum i)]
    exact hx

/-- **Hilbert's tenth problem is undecidable, for solutions in the integers.**  There is a
polynomial `Q` with integer coefficients such that no algorithm decides, for a given natural
number `a`, whether `Q (a, y₁, …, yₙ) = 0` has a solution in integers. -/
theorem hilbert10_undecidable_int :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℤ),
      ¬ ComputablePred fun a : ℕ => ∃ y : Fin n → ℤ,
          MvPolynomial.eval (Fin.cons (a : ℤ) y) Q = 0 := by
  obtain ⟨m, P, hP⟩ := exists_poly_of_dioph Halts (dioph_of_rePred Halts halts_re)
  refine ⟨m * 4, bind₁ fourSq P, fun h => halts_not_computable (ComputablePred.of_eq h ?_)⟩
  intro a
  rw [exists_int_iff_exists_nat]
  exact hP a

end CS

import Mathlib

/-!
# Auxiliary Diophantine machinery towards the MRDP theorem

This file develops arithmetic tools used in the proof that every recursively enumerable
predicate is Diophantine (the MRDP theorem), on top of Mathlib's `Dioph` API and
Matiyasevich's theorem `Dioph.pow_dioph`.

The main ingredients are:

* `CS.choose_eq_div_mod` / `CS.choose_dioph`: binomial coefficients are Diophantine;
* `CS.factorial_eq_div` / `CS.factorial_dioph`: the factorial is Diophantine;
* `CS.prime_dioph`: primality is Diophantine (via Wilson's theorem);
* `CS.exists_crt_code`: Gödel-style coding of a finite sequence with a common modulus base;
* `CS.poly_int_modEq`: polynomials respect congruences;
* `CS.exists_majorant`: every polynomial admits a monotone nonnegative majorant;
* `CS.dioph_fin`: a Diophantine set can be described with finitely many witness variables.

The bounded universal quantifier itself is proved in `RequestProject.Davis`.
-/

open Dioph Nat

namespace CS

/-! ### Binomial coefficients -/

/-- Digit extraction formula for binomial coefficients: writing `(u+1)^n` in base `u` exposes
the binomial coefficients `n.choose k` as its digits, as soon as `2 ^ n < u`. -/
theorem choose_eq_div_mod_gen (n u : ℕ) (hu : 2 ^ n < u) (k : ℕ) :
    ((u + 1) ^ n / u ^ k) % u = n.choose k := by
  set S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (n + 1 - k), u ^ j * n.choose (j + k) with hS
  have hu0 : 0 < u := lt_of_le_of_lt (Nat.zero_le _) hu
  have hSlt : ∀ k, n.choose k < u := fun k => lt_of_le_of_lt (Nat.choose_le_two_pow n k) hu
  have hS0 : S 0 = (u + 1) ^ n := by
    simp only [hS, Nat.sub_zero, Nat.add_zero]
    rw [add_pow]; simp
  have hstep : ∀ k, k ≤ n → S k = n.choose k + u * S (k + 1) := by
    intro k hk
    have h1 : n + 1 - k = (n - k) + 1 := by omega
    have h2 : n + 1 - (k + 1) = n - k := by omega
    simp only [hS, h1, h2]
    rw [Finset.sum_range_succ', Finset.mul_sum, Nat.add_comm]
    congr 1
    · simp
    · exact Finset.sum_congr rfl fun i _ => by ring_nf
  have hSbig : ∀ k, n < k → S k = 0 := by
    intro k hk
    have h : n + 1 - k = 0 := by omega
    simp [hS, h]
  have hdiv : ∀ k, (u + 1) ^ n / u ^ k = S k := by
    intro k
    induction k with
    | zero => simp [hS0]
    | succ k ih =>
        rw [pow_succ, ← Nat.div_div_eq_div_mul, ih]
        rcases le_or_gt k n with hk | hk
        · rw [hstep k hk, Nat.add_mul_div_left _ _ hu0, Nat.div_eq_of_lt (hSlt k)]
          omega
        · rw [hSbig k hk, hSbig (k + 1) (by omega)]
          simp
  rw [hdiv]
  rcases le_or_gt k n with hk | hk
  · rw [hstep k hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hSlt k)]
  · rw [hSbig k hk, Nat.choose_eq_zero_of_lt hk]
    simp

/-- Explicit arithmetic formula for the binomial coefficient. -/
theorem choose_eq_div_mod (n k : ℕ) :
    n.choose k = ((2 ^ n + 1 + 1) ^ n / (2 ^ n + 1) ^ k) % (2 ^ n + 1) :=
  (choose_eq_div_mod_gen n (2 ^ n + 1) (by omega) k).symm

/-- Binomial coefficients form a Diophantine function. -/
theorem choose_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have hu : DiophFn fun v => 2 ^ f v + 1 :=
    Dioph.add_dioph (Dioph.pow_dioph (Dioph.const_dioph 2) df) (Dioph.const_dioph 1)
  have hnum : DiophFn fun v => (2 ^ f v + 1 + 1) ^ f v :=
    Dioph.pow_dioph (Dioph.add_dioph hu (Dioph.const_dioph 1)) df
  have hden : DiophFn fun v => (2 ^ f v + 1) ^ g v := Dioph.pow_dioph hu dg
  have hmain := Dioph.mod_dioph (Dioph.div_dioph hnum hden) hu
  have heq : (fun v => (f v).choose (g v))
      = fun v => ((2 ^ f v + 1 + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) :=
    funext fun v => choose_eq_div_mod _ _
  rw [heq]
  exact hmain

/-! ### Factorials -/

/-- The descending factorial `r (r-1) ⋯ (r-n+1)` is close to `r ^ n`. -/
theorem pow_le_descFactorial_add (r : ℕ) : ∀ n, n ≤ r →
    r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ r := by omega
      have h1 := ih hn'
      have hDle : r.descFactorial n ≤ r ^ n := Nat.descFactorial_le_pow r n
      have hkey : r ^ n * r ≤ (r.descFactorial n + n ^ 2 * r ^ (n - 1)) * r :=
        Nat.mul_le_mul_right _ h1
      have hpow : n ^ 2 * r ^ (n - 1) * r = n ^ 2 * r ^ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · rw [mul_assoc]
          congr 1
          rw [← pow_succ]
          congr 1
          omega
      have hsplit : r.descFactorial n * r = r.descFactorial (n + 1) + n * r.descFactorial n := by
        rw [Nat.descFactorial_succ r n]
        have hr : r = (r - n) + n := by omega
        calc r.descFactorial n * r = r.descFactorial n * ((r - n) + n) := by rw [← hr]
          _ = (r - n) * r.descFactorial n + n * r.descFactorial n := by ring
      calc r ^ (n + 1) = r ^ n * r := by ring
        _ ≤ (r.descFactorial n + n ^ 2 * r ^ (n - 1)) * r := hkey
        _ = r.descFactorial n * r + n ^ 2 * r ^ (n - 1) * r := by ring
        _ = r.descFactorial (n + 1) + n * r.descFactorial n + n ^ 2 * r ^ n := by
              rw [hsplit, hpow]
        _ ≤ r.descFactorial (n + 1) + n * r ^ n + n ^ 2 * r ^ n := by gcongr
        _ ≤ r.descFactorial (n + 1) + (n + 1) ^ 2 * r ^ ((n + 1) - 1) := by
              simp only [Nat.add_sub_cancel]
              nlinarith [Nat.zero_le (r ^ n)]

/-- For sufficiently large `r`, the factorial is a quotient of a power by a binomial
coefficient. -/
theorem factorial_eq_div (n r : ℕ) (hr : n ^ 2 * ((n)! + 1) < r) :
    (n)! = r ^ n / r.choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnr : n ≤ r := by nlinarith [Nat.factorial_pos n, sq_nonneg n]
  have hr0 : 0 < r := by omega
  have hD : r.descFactorial n = (n)! * r.choose n := Nat.descFactorial_eq_factorial_mul_choose r n
  have h1 : (n)! * r.choose n ≤ r ^ n := by
    rw [← hD]; exact Nat.descFactorial_le_pow r n
  have h2 : r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := pow_le_descFactorial_add r n hnr
  have hpow : r ^ n = r * r ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hp : 0 < r ^ (n - 1) := Nat.pow_pos hr0
  have hstrict : ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) < r ^ n := by
    rw [hpow]
    calc ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) = (n ^ 2 * ((n)! + 1)) * r ^ (n - 1) := by ring
      _ < r * r ^ (n - 1) := Nat.mul_lt_mul_of_lt_of_le hr (le_refl _) hp
  have hkey : n ^ 2 * r ^ (n - 1) < r.choose n := by
    have hlt : (n)! * (n ^ 2 * r ^ (n - 1)) < (n)! * r.choose n := by
      have hsum : (n)! * (n ^ 2 * r ^ (n - 1)) + n ^ 2 * r ^ (n - 1) < r ^ n := by
        calc (n)! * (n ^ 2 * r ^ (n - 1)) + n ^ 2 * r ^ (n - 1)
            = ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) := by ring
          _ < r ^ n := hstrict
      omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine (Nat.div_eq_of_lt_le h1 ?_).symm
  calc r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := h2
    _ = (n)! * r.choose n + n ^ 2 * r ^ (n - 1) := by rw [hD]
    _ < (n)! * r.choose n + r.choose n := by omega
    _ = ((n)! + 1) * r.choose n := by ring

/-- An explicit admissible choice of the parameter `r` in `CS.factorial_eq_div`. -/
theorem factorial_bound (n : ℕ) : n ^ 2 * ((n)! + 1) < (n + 1) ^ (n + 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (n)! + 1 ≤ (n + 1) ^ n := by
    have ha : (n)! ≤ n ^ n := Nat.factorial_le_pow n
    have hb : n ^ n < (n + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  have h2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc n ^ 2 * ((n)! + 1) ≤ (n + 1) ^ 2 * (n + 1) ^ n := Nat.mul_le_mul h2 h1
    _ = (n + 1) ^ (n + 2) := by rw [← pow_add]; congr 1; omega
    _ < (n + 1) ^ (n + 3) := Nat.pow_lt_pow_right (by omega) (by omega)

/-- Closed arithmetic formula for the factorial. -/
theorem factorial_eq (n : ℕ) :
    (n)! = ((n + 1) ^ (n + 3)) ^ n / ((n + 1) ^ (n + 3)).choose n :=
  factorial_eq_div n _ (factorial_bound n)

/-- The factorial is a Diophantine function. -/
theorem factorial_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    DiophFn fun v => (f v)! := by
  have hr : DiophFn fun v => (f v + 1) ^ (f v + 3) :=
    Dioph.pow_dioph (Dioph.add_dioph df (Dioph.const_dioph 1))
      (Dioph.add_dioph df (Dioph.const_dioph 3))
  have hnum : DiophFn fun v => ((f v + 1) ^ (f v + 3)) ^ f v := Dioph.pow_dioph hr df
  have hmain := Dioph.div_dioph hnum (choose_dioph hr df)
  have heq : (fun v => (f v)!)
      = fun v => ((f v + 1) ^ (f v + 3)) ^ f v / ((f v + 1) ^ (f v + 3)).choose (f v) :=
    funext fun v => factorial_eq _
  rw [heq]
  exact hmain

/-- Wilson's theorem as a Diophantine-friendly characterisation of primality. -/
theorem prime_iff_dvd_factorial (p : ℕ) : Nat.Prime p ↔ (1 < p ∧ p ∣ ((p - 1)! + 1)) := by
  constructor
  · intro hp
    have hne : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨hp.one_lt, ?_⟩
    have h := (Nat.prime_iff_fac_equiv_neg_one (n := p) hp.ne_one).1 hp
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by push_cast [h]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  · rintro ⟨h1, h2⟩
    have hne : NeZero p := ⟨by omega⟩
    refine (Nat.prime_iff_fac_equiv_neg_one (n := p) (by omega)).2 ?_
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    push_cast at h0
    linear_combination h0

/-- Primality is a Diophantine predicate (Wilson's theorem). -/
theorem prime_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    Dioph {v | Nat.Prime (f v)} := by
  have h1 : Dioph {v : α → ℕ | 1 < f v} := Dioph.lt_dioph (Dioph.const_dioph 1) df
  have h2 : Dioph {v : α → ℕ | f v ∣ ((f v - 1)! + 1)} :=
    Dioph.dvd_dioph df
      (Dioph.add_dioph (factorial_dioph (Dioph.sub_dioph df (Dioph.const_dioph 1)))
        (Dioph.const_dioph 1))
  refine Dioph.ext (Dioph.inter h1 h2) fun v => ?_
  simpa using (prime_iff_dvd_factorial (f v)).symm

/-! ### Coding of finite sequences -/

/-- Gödel-style coding of a finite sequence: if the modulus base `b` is divisible by `n !`
(which makes the moduli `1 + (i+1) * b` pairwise coprime) and dominates the entries, then a
single number `a` codes the sequence via `a % (1 + (i+1) * b)`. -/
theorem exists_crt_code (x : ℕ → ℕ) (n b : ℕ) (hb : (n)! ∣ b)
    (hlt : ∀ i ≤ n, x i < 1 + (i + 1) * b) :
    ∃ a, ∀ i ≤ n, a % (1 + (i + 1) * b) = x i := by
  set s : ℕ → ℕ := fun i => 1 + (i + 1) * b with hs
  have hco : (List.range (n + 1)).Pairwise (Function.onFun Nat.Coprime s) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_range, Function.onFun, hs]
    have hjn : (j : ℕ) ≤ n := by have := j.2; simp at this; omega
    have hij' : (i : ℕ) < (j : ℕ) := by exact_mod_cast hij
    have hdvd : ((j : ℕ) + 1) - ((i : ℕ) + 1) ∣ b := by
      have h1 : (j : ℕ) - (i : ℕ) ∣ (n)! := by
        refine Nat.dvd_factorial ?_ ?_ <;> omega
      have h2 : ((j : ℕ) + 1) - ((i : ℕ) + 1) = (j : ℕ) - (i : ℕ) := by omega
      rw [h2]
      exact h1.trans hb
    simpa [Nat.add_comm] using Nat.coprime_mul_succ hdvd
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfList x s (List.range (n + 1)) hco
  refine ⟨k, fun i hi => ?_⟩
  have hmem : i ∈ List.range (n + 1) := by simp; omega
  calc k % (1 + (i + 1) * b) = k % s i := rfl
    _ = x i % s i := hk i hmem
    _ = x i := Nat.mod_eq_of_lt (hlt i hi)

/-! ### Polynomials, congruences and majorants -/

/-- Polynomials respect congruences of their arguments. -/
theorem poly_int_modEq {γ : Type} (p : Poly γ) (m : ℕ) (v w : γ → ℕ)
    (h : ∀ i, (v i : ℤ) ≡ (w i : ℤ) [ZMOD (m : ℤ)]) :
    (p v : ℤ) ≡ p w [ZMOD (m : ℤ)] := by
  obtain ⟨F, hF⟩ := p
  show F v ≡ F w [ZMOD (m : ℤ)]
  induction hF with
  | proj i => exact h i
  | const n => exact Int.ModEq.refl _
  | sub _ _ ih1 ih2 => exact Int.ModEq.sub ih1 ih2
  | mul _ _ ih1 ih2 => exact Int.ModEq.mul ih1 ih2

/-- Every polynomial has a monotone, nonnegative polynomial majorant. -/
theorem exists_majorant' {γ : Type} : ∀ {F : (γ → ℕ) → ℤ}, IsPoly F →
    ∃ q : Poly γ, (∀ v, 0 ≤ q v) ∧ (∀ v, |F v| ≤ q v) ∧
      ∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w := by
  intro F hF
  induction hF with
  | proj i =>
      exact ⟨Poly.proj i, fun v => by simp, fun v => by simp, fun v w hvw => by simpa using hvw i⟩
  | const n =>
      exact ⟨Poly.const |n|, fun v => by simp, fun v => by simp, fun v w _ => le_refl _⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hp1, hm1⟩ := ih1
      obtain ⟨q2, hq2, hp2, hm2⟩ := ih2
      refine ⟨q1 + q2, fun v => by
        have := hq1 v; have := hq2 v; simp only [Poly.add_apply]; positivity,
        fun v => ?_, fun v w hvw => ?_⟩
      · simp only [Poly.add_apply]
        calc |_| ≤ |_| + |_| := abs_sub _ _
          _ ≤ q1 v + q2 v := by gcongr <;> [exact hp1 v; exact hp2 v]
      · simp only [Poly.add_apply]
        exact add_le_add (hm1 v w hvw) (hm2 v w hvw)
  | mul _ _ ih1 ih2 =>
      obtain ⟨q1, hq1, hp1, hm1⟩ := ih1
      obtain ⟨q2, hq2, hp2, hm2⟩ := ih2
      refine ⟨q1 * q2, fun v => mul_nonneg (hq1 v) (hq2 v), fun v => ?_, fun v w hvw => ?_⟩
      · simp only [Poly.mul_apply, abs_mul]
        exact mul_le_mul (hp1 v) (hp2 v) (abs_nonneg _) (hq1 v)
      · simp only [Poly.mul_apply]
        exact mul_le_mul (hm1 v w hvw) (hm2 v w hvw) (hq2 v) (le_trans (hq1 v) (hm1 v w hvw))

/-- Every polynomial has a monotone, nonnegative polynomial majorant. -/
theorem exists_majorant {γ : Type} (p : Poly γ) :
    ∃ q : Poly γ, (∀ v, 0 ≤ q v) ∧ (∀ v, |p v| ≤ q v) ∧
      ∀ v w : γ → ℕ, (∀ i, v i ≤ w i) → q v ≤ q w :=
  exists_majorant' p.isPoly

/-! ### Products of arithmetic progressions -/

/-- The product `∏_{k=1}^{y} (1 + k * b)`. -/
def progProd (y b : ℕ) : ℕ := ∏ k ∈ Finset.range y, (1 + (k + 1) * b)

@[simp] theorem progProd_zero (b : ℕ) : progProd 0 b = 1 := by simp [progProd]

theorem progProd_pos (y b : ℕ) : 0 < progProd y b :=
  Finset.prod_pos fun _ _ => by omega

theorem dvd_progProd {y b k : ℕ} (hk : k < y) : 1 + (k + 1) * b ∣ progProd y b :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hk)

theorem progProd_lt (y b : ℕ) (hb : 0 < b) : progProd y b < b * (1 + y * b) ^ (y + 1) + 1 := by
  have h1 : progProd y b ≤ (1 + y * b) ^ y := by
    unfold progProd
    calc ∏ k ∈ Finset.range y, (1 + (k + 1) * b) ≤ ∏ _k ∈ Finset.range y, (1 + y * b) := by
          refine Finset.prod_le_prod' ?_
          intro i hi
          simp only [Finset.mem_range] at hi
          have : (i + 1) * b ≤ y * b := Nat.mul_le_mul_right _ (by omega)
          omega
      _ = (1 + y * b) ^ y := by simp
  have h2 : (1 + y * b) ^ y ≤ b * (1 + y * b) ^ (y + 1) :=
    le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.le_mul_of_pos_left _ hb)
  omega

/-- The key congruence making `progProd` Diophantine: modulo a suitable large modulus, the
product of the arithmetic progression is a power times a descending factorial. -/
theorem progProd_eq (y b m : ℕ) (hb : 0 < b) (hm : y ≤ m)
    (hcong : b * m ≡ 1 + y * b [MOD (b * (1 + y * b) ^ (y + 1) + 1)]) :
    progProd y b = (b ^ y * m.descFactorial y) % (b * (1 + y * b) ^ (y + 1) + 1) := by
  set M := b * (1 + y * b) ^ (y + 1) + 1 with hM
  have hZ : ((b ^ y * m.descFactorial y : ℕ) : ℤ)
      = ∏ j ∈ Finset.range y, ((b : ℤ) * m - j * b) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    have hbp : (b : ℤ) ^ y = ∏ _j ∈ Finset.range y, (b : ℤ) := by simp
    rw [hbp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have hjm : j ≤ m := by omega
    have hc : ((m - j : ℕ) : ℤ) = (m : ℤ) - j := by push_cast [hjm]; omega
    rw [hc]; ring
  have hc : ((b * m : ℕ) : ℤ) ≡ ((1 + y * b : ℕ) : ℤ) [ZMOD (M : ℤ)] :=
    Int.natCast_modEq_iff.mpr hcong
  push_cast at hc
  have hprod : ∏ j ∈ Finset.range y, ((b : ℤ) * m - j * b)
      ≡ ∏ j ∈ Finset.range y, ((1 + (y : ℤ) * b) - j * b) [ZMOD (M : ℤ)] :=
    Int.ModEq.prod fun j _ => Int.ModEq.sub hc (Int.ModEq.refl _)
  have hrefl : ∏ j ∈ Finset.range y, ((1 + (y : ℤ) * b) - j * b) = ((progProd y b : ℕ) : ℤ) := by
    unfold progProd
    push_cast
    rw [← Finset.prod_range_reflect (fun k => (1 : ℤ) + ((k : ℤ) + 1) * b) y]
    refine Finset.prod_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have h1 : ((y - 1 - j : ℕ) : ℤ) = (y : ℤ) - 1 - j := by
      have : j ≤ y - 1 := by omega
      push_cast [this]
      omega
    rw [h1]; ring
  have hfinal : ((progProd y b : ℕ) : ℤ) ≡ ((b ^ y * m.descFactorial y : ℕ) : ℤ) [ZMOD (M : ℤ)] := by
    rw [hZ, ← hrefl]; exact hprod.symm
  have hnat : progProd y b ≡ b ^ y * m.descFactorial y [MOD M] := Int.natCast_modEq_iff.mp hfinal
  have hlt := progProd_lt y b hb
  unfold Nat.ModEq at hnat
  rw [← hnat, Nat.mod_eq_of_lt (by omega)]

/-- The auxiliary variable in the Diophantine description of `progProd` always exists. -/
theorem exists_progProd_witness (y b : ℕ) (hb : 0 < b) :
    ∃ m, y ≤ m ∧ b * m ≡ 1 + y * b [MOD (b * (1 + y * b) ^ (y + 1) + 1)] := by
  set M := b * (1 + y * b) ^ (y + 1) + 1 with hM
  have hM1 : 1 < M := by
    have h1 : 1 ≤ (1 + y * b) ^ (y + 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : b ≤ b * (1 + y * b) ^ (y + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcop : Nat.Coprime b M := by rw [hM]; simp
  obtain ⟨m₀, _, hm₀⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
  refine ⟨m₀ * (1 + y * b) + M * y, ?_, ?_⟩
  · have : y ≤ M * y := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have h1 : b * m₀ ≡ 1 [MOD M] := by
      unfold Nat.ModEq
      rw [hm₀, Nat.one_mod_eq_one.mpr (by omega)]
    calc b * (m₀ * (1 + y * b) + M * y) = (b * m₀) * (1 + y * b) + M * (b * y) := by ring
      _ ≡ 1 * (1 + y * b) + M * (b * y) [MOD M] := Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ h1)
      _ = (1 + y * b) + M * (b * y) := by ring
      _ ≡ (1 + y * b) + 0 [MOD M] := Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr ⟨b * y, rfl⟩)
      _ = 1 + y * b := by ring

/-- Products of arithmetic progressions are Diophantine (Davis' lemma). -/
theorem progProd_dioph {α : Type} {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g)
    (hg : ∀ v, 0 < g v) : DiophFn fun v => progProd (f v) (g v) := by
  set F : (Option (Option α) → ℕ) → ℕ := fun u => f (u ∘ some ∘ some) with hF
  set G : (Option (Option α) → ℕ) → ℕ := fun u => g (u ∘ some ∘ some) with hG
  have dF : DiophFn F := Dioph.reindex_diophFn (some ∘ some) df
  have dG : DiophFn G := Dioph.reindex_diophFn (some ∘ some) dg
  have dZ : DiophFn fun u : Option (Option α) → ℕ => u (some none) := Dioph.proj_dioph _
  have dM : DiophFn fun u : Option (Option α) → ℕ => u none := Dioph.proj_dioph _
  have dMM : DiophFn fun u : Option (Option α) → ℕ => G u * (1 + F u * G u) ^ (F u + 1) + 1 :=
    Dioph.add_dioph (Dioph.mul_dioph dG (Dioph.pow_dioph
      (Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph dF dG))
      (Dioph.add_dioph dF (Dioph.const_dioph 1)))) (Dioph.const_dioph 1)
  have dC1 : Dioph {u : Option (Option α) → ℕ | F u ≤ u none} := Dioph.le_dioph dF dM
  have dC2 : Dioph {u : Option (Option α) → ℕ |
      G u * u none ≡ 1 + F u * G u [MOD (G u * (1 + F u * G u) ^ (F u + 1) + 1)]} :=
    Dioph.modEq_dioph (Dioph.mul_dioph dG dM)
      (Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph dF dG)) dMM
  have dC3 : Dioph {u : Option (Option α) → ℕ | u (some none) =
      (G u ^ F u * ((F u)! * (u none).choose (F u))) %
        (G u * (1 + F u * G u) ^ (F u + 1) + 1)} :=
    Dioph.eq_dioph dZ (Dioph.mod_dioph (Dioph.mul_dioph (Dioph.pow_dioph dG dF)
      (Dioph.mul_dioph (factorial_dioph dF) (choose_dioph dM dF))) dMM)
  refine Dioph.ext (Dioph.ex1_dioph ((dC1.inter dC2).inter dC3)) ?_
  intro w
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hF, hG]
  constructor
  · rintro ⟨m, ⟨⟨h1, h2⟩, h3⟩⟩
    have hcomp : (Option.elim' m w ∘ some ∘ some) = w ∘ some := rfl
    rw [hcomp] at h1 h2 h3
    have hd : m.descFactorial (f (w ∘ some)) = (f (w ∘ some))! * m.choose (f (w ∘ some)) :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hpp := progProd_eq (f (w ∘ some)) (g (w ∘ some)) m (hg _) h1 h2
    rw [hd] at hpp
    exact hpp.trans h3.symm
  · intro h
    obtain ⟨m, hm1, hm2⟩ := exists_progProd_witness (f (w ∘ some)) (g (w ∘ some)) (hg _)
    refine ⟨m, ⟨⟨hm1, hm2⟩, ?_⟩⟩
    have hcomp : (Option.elim' m w ∘ some ∘ some) = w ∘ some := rfl
    rw [hcomp]
    have hd : m.descFactorial (f (w ∘ some)) = (f (w ∘ some))! * m.choose (f (w ∘ some)) :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hpp := progProd_eq (f (w ∘ some)) (g (w ∘ some)) m (hg _) hm1 hm2
    rw [hd] at hpp
    show w none = _
    rw [← h]
    exact hpp

/-! ### Divisibility helpers for descending factorials -/

/-- If `a` is congruent mod `m` to some `x ≤ u`, then `m` divides the descending factorial
`a (a-1) ⋯ (a-u)`. -/
theorem dvd_descFactorial_of_modEq {a x u m : ℕ} (h : a ≡ x [MOD m]) (hxu : x ≤ u) :
    m ∣ a.descFactorial (u + 1) := by
  rcases lt_or_ge a x with hax | hax
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (show a < u + 1 by omega)]
    exact dvd_zero m
  · rw [Nat.descFactorial_eq_prod_range]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => a - i)
      (Finset.mem_range.2 (show x < u + 1 by omega)))
    exact (Nat.modEq_iff_dvd' hax).mp h.symm

/-- Conversely, if a prime `P > u` divides `a (a-1) ⋯ (a-u)` then the residue of `a` mod `P`
is at most `u`. -/
theorem mod_le_of_prime_dvd_descFactorial {P a u : ℕ} (hp : P.Prime) (hu : u < P)
    (h : P ∣ a.descFactorial (u + 1)) : a % P ≤ u := by
  rw [Nat.descFactorial_eq_prod_range] at h
  obtain ⟨j, hj, hdvd⟩ := (Nat.Prime.prime hp).dvd_finset_prod_iff _ |>.mp h
  simp only [Finset.mem_range] at hj
  rcases lt_or_ge a j with haj | haj
  · have : a % P = a := Nat.mod_eq_of_lt (by omega)
    omega
  · have hm : a ≡ j [MOD P] := ((Nat.modEq_iff_dvd' haj).mpr hdvd).symm
    have h2 : a % P = j % P := hm
    rw [h2, Nat.mod_eq_of_lt (by omega)]
    omega

/-- If all the factors `1 + (k+1) b`, `k < y`, divide `N`, then so does their product; the
hypothesis on `b` guarantees that these factors are pairwise coprime. -/
theorem progProd_dvd_of_forall {b N : ℕ} : ∀ {y : ℕ}, (∀ d, 0 < d → d ≤ y → d ∣ b) →
    (∀ k < y, 1 + (k + 1) * b ∣ N) → progProd y b ∣ N := by
  intro y
  induction y with
  | zero => intro _ _; simp [progProd]
  | succ y ih =>
      intro hb h
      have hco : Nat.Coprime (progProd y b) (1 + (y + 1) * b) := by
        refine Nat.Coprime.prod_left ?_
        intro k hk
        simp only [Finset.mem_range] at hk
        have hd : (y + 1) - (k + 1) ∣ b := hb _ (by omega) (by omega)
        simpa [Nat.add_comm] using Nat.coprime_mul_succ hd
      have h1 : progProd y b ∣ N :=
        ih (fun d hd hdy => hb d hd (by omega)) (fun k hk => h k (by omega))
      have h2 : 1 + (y + 1) * b ∣ N := h y (by omega)
      have hsplit : progProd (y + 1) b = progProd y b * (1 + (y + 1) * b) := by
        simp [progProd, Finset.prod_range_succ]
      rw [hsplit]
      exact hco.mul_dvd_of_dvd_of_dvd h1 h2

/-! ### Finitely many Diophantine conditions -/

/-- A finite family of Diophantine conditions is Diophantine. -/
theorem dioph_forall_fin {α : Type} : ∀ (n : ℕ) (S : Fin n → Set (α → ℕ)), (∀ i, Dioph (S i)) →
    Dioph {v | ∀ i, v ∈ S i} := by
  intro n
  induction n with
  | zero =>
      intro S _
      have he : {v : α → ℕ | ∀ i : Fin 0, v ∈ S i} = Set.univ := by ext v; simp
      rw [he]
      exact Dioph.of_no_dummies _ (Poly.const 0)
        (fun v => iff_of_true trivial (by simp [Poly.const_apply]))
  | succ n ih =>
      intro S d
      have hd := (ih (fun i => S i.succ) (fun i => d i.succ)).inter (d 0)
      refine Dioph.ext hd fun v => ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ⟨h1, h2⟩ i => Fin.cases h2 (fun j => h1 j) i, fun h => ⟨fun j => h j.succ, h 0⟩⟩

/-! ### Normalising the number of witness variables -/

/-- A polynomial depends on only finitely many of its variables. -/
theorem isPoly_support {γ : Type} : ∀ {F : (γ → ℕ) → ℤ}, IsPoly F →
    ∃ s : Finset γ, ∀ v w : γ → ℕ, (∀ i ∈ s, v i = w i) → F v = F w := by
  classical
  intro F hF
  induction hF with
  | proj i =>
      exact ⟨{i}, fun v w h => by show ((v i : ℤ)) = (w i : ℤ); rw [h i (by simp)]⟩
  | const n => exact ⟨∅, fun v w _ => rfl⟩
  | sub _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      show _ - _ = _ - _
      rw [h1 v w (fun i hi => h i (by simp [hi])), h2 v w (fun i hi => h i (by simp [hi]))]
  | mul _ _ ih1 ih2 =>
      obtain ⟨s1, h1⟩ := ih1; obtain ⟨s2, h2⟩ := ih2
      refine ⟨s1 ∪ s2, fun v w h => ?_⟩
      show _ * _ = _ * _
      rw [h1 v w (fun i hi => h i (by simp [hi])), h2 v w (fun i hi => h i (by simp [hi]))]

/-- Every Diophantine set can be described using only finitely many witness variables. -/
theorem dioph_fin {α : Type} {S : Set (α → ℕ)} (d : Dioph S) :
    ∃ (n : ℕ) (p : Poly (α ⊕ Fin n)), ∀ v, v ∈ S ↔ ∃ t : Fin n → ℕ, p (Sum.elim v t) = 0 := by
  classical
  obtain ⟨β, p, hp⟩ := d
  obtain ⟨s, hs⟩ := isPoly_support p.isPoly
  set s' : Finset β := s.preimage Sum.inr (Sum.inr_injective.injOn) with hs'
  set n : ℕ := s'.card with hn
  set e : {x // x ∈ s'} ≃ Fin n := s'.equivFin with he
  set idx : β → Fin (n + 1) := fun b => if h : b ∈ s' then (e ⟨b, h⟩).castSucc else Fin.last n
    with hidx
  refine ⟨n + 1, p.map (Sum.map id idx), fun v => (hp v).trans ?_⟩
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun j => if h : (j : ℕ) < n then t (e.symm ⟨(j : ℕ), h⟩) else 0, ?_⟩
    rw [Poly.map_apply]
    refine (hs _ _ ?_).trans ht
    rintro (a | b) hb
    · rfl
    · have hb' : b ∈ s' := by rw [hs']; simpa using hb
      have hib : idx b = (e ⟨b, hb'⟩).castSucc := by rw [hidx]; simp [hb']
      simp only [Function.comp_apply, Sum.map_inr, hib, Sum.elim_inr, Fin.val_castSucc]
      rw [dif_pos (e ⟨b, hb'⟩).isLt]
      congr 1
      have hcast : (⟨((e ⟨b, hb'⟩ : Fin n) : ℕ), (e ⟨b, hb'⟩).isLt⟩ : Fin n) = e ⟨b, hb'⟩ := rfl
      rw [hcast, Equiv.symm_apply_apply]
  · rintro ⟨u, hu⟩
    refine ⟨fun b => u (idx b), ?_⟩
    rw [Poly.map_apply] at hu
    refine Eq.trans ?_ hu
    congr 1
    funext x
    rcases x with a | b <;> rfl

end CS

import RequestProject.Davis

/-!
# The MRDP theorem

Building on Matiyasevich's theorem (`Dioph.pow_dioph`, in Mathlib) and on Davis' bounded
universal quantifier (`CS.forall_lt_dioph`), we show here that every partial recursive
function has a Diophantine graph, and hence that every recursively enumerable predicate is
Diophantine.
-/

open Dioph Nat Sum Vector3

namespace CS

/-! ### Gödel's β function -/

/-- Gödel's β function, used to code finite sequences by a pair of numbers. -/
def beta (c d i : ℕ) : ℕ := c % (1 + (i + 1) * d)

/-- Every finite sequence is coded by Gödel's β function. -/
theorem exists_beta (s : ℕ → ℕ) (x : ℕ) : ∃ c d, ∀ i ≤ x, beta c d i = s i := by
  classical
  set M : ℕ := max x ((Finset.range (x + 1)).sup s) with hM
  set b : ℕ := M ! with hb
  have hMb : M ≤ b := Nat.self_le_factorial _
  have hxfac : (x)! ∣ b := Nat.factorial_dvd_factorial (le_max_left _ _)
  have hlt : ∀ i ≤ x, s i < 1 + (i + 1) * b := by
    intro i hi
    have h1 : s i ≤ M := le_trans (Finset.le_sup (f := s) (Finset.mem_range.2 (by omega)))
      (le_max_right _ _)
    have h2 : b ≤ (i + 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨c, hc⟩ := exists_crt_code s x b hxfac hlt
  exact ⟨c, b, fun i hi => hc i hi⟩

theorem beta_dioph {α : Type} {c d i : (α → ℕ) → ℕ} (dc : DiophFn c) (dd : DiophFn d)
    (di : DiophFn i) : DiophFn fun v => beta (c v) (d v) (i v) :=
  Dioph.mod_dioph dc (Dioph.add_dioph (Dioph.const_dioph 1)
    (Dioph.mul_dioph (Dioph.add_dioph di (Dioph.const_dioph 1)) dd))

/-! ### Composition -/

/-- Composition of a Diophantine function of `n+2` arguments with Diophantine functions. -/
theorem diophFn_comp_cons2 {α : Type} {n : ℕ} {G : Vector3 ℕ (n + 2) → ℕ} (dG : DiophFn G)
    {a b : (α → ℕ) → ℕ} {w : Fin2 n → (α → ℕ) → ℕ}
    (da : DiophFn a) (db : DiophFn b) (dw : ∀ i, DiophFn (w i)) :
    DiophFn (fun v => G (Vector3.cons (a v) (Vector3.cons (b v) (fun i => w i v)))) := by
  have hall : VectorAllP DiophFn (Vector3.cons a (Vector3.cons b w)) := by
    refine (vectorAllP_iff_forall _ _).2 ?_
    intro i
    cases i with
    | fz => exact da
    | fs j =>
        cases j with
        | fz => exact db
        | fs k => exact dw k
  have h := Dioph.diophFn_comp dG (Vector3.cons a (Vector3.cons b w)) hall
  refine cast (congrArg DiophFn ?_) h
  funext v
  congr 1
  funext i
  cases i with
  | fz => rfl
  | fs j => cases j with
    | fz => rfl
    | fs k => rfl

/-! ### Primitive recursion -/

/-- Primitive recursion, in `Vector3` form. -/
def precFn {n : ℕ} (F : Vector3 ℕ n → ℕ) (G : Vector3 ℕ (n + 2) → ℕ) (w : Vector3 ℕ n) :
    ℕ → ℕ
  | 0 => F w
  | (y + 1) => G (Vector3.cons y (Vector3.cons (precFn F G w y) w))

/-- The graph of a primitive recursion is described by an existential formula, using Gödel's
β function to code the whole course of the computation. -/
theorem precFn_iff {n : ℕ} (F : Vector3 ℕ n → ℕ) (G : Vector3 ℕ (n + 2) → ℕ)
    (w : Vector3 ℕ n) (x z : ℕ) :
    precFn F G w x = z ↔ ∃ c d, beta c d 0 = F w ∧
      (∀ i < x, beta c d (i + 1) = G (Vector3.cons i (Vector3.cons (beta c d i) w))) ∧
      beta c d x = z := by
  constructor
  · rintro rfl
    obtain ⟨c, d, hcd⟩ := exists_beta (precFn F G w) x
    refine ⟨c, d, ?_, ?_, hcd x le_rfl⟩
    · rw [hcd 0 (Nat.zero_le _)]; rfl
    · intro i hi
      rw [hcd (i + 1) (by omega), hcd i (by omega)]
      rfl
  · rintro ⟨c, d, h0, hstep, hx⟩
    have key : ∀ i ≤ x, beta c d i = precFn F G w i := by
      intro i
      induction i with
      | zero => intro _; exact h0
      | succ i ih =>
          intro hi
          rw [hstep i (by omega), ih (by omega)]
          rfl
    rw [← hx, key x le_rfl]

/-- Primitive recursion preserves Diophantine functions. -/
theorem precFn_dioph {n : ℕ} {F : Vector3 ℕ n → ℕ} {G : Vector3 ℕ (n + 2) → ℕ}
    (dF : DiophFn F) (dG : DiophFn G) :
    DiophFn (fun v : Vector3 ℕ (n + 1) => precFn F G (fun i => v (Fin2.fs i)) (v Fin2.fz)) := by
  set S : Set (Option (Fin2 (n + 4)) → ℕ) :=
    {t | beta (t (some (Fin2.fs Fin2.fz))) (t (some Fin2.fz)) (t none + 1) =
      G (Vector3.cons (t none) (Vector3.cons
        (beta (t (some (Fin2.fs Fin2.fz))) (t (some Fin2.fz)) (t none))
        (fun i => t (some (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i))))))))} with hS
  have dS : Dioph S := by
    refine Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _)
      (Dioph.add_dioph (Dioph.proj_dioph none) (Dioph.const_dioph 1))) ?_
    exact diophFn_comp_cons2 dG (Dioph.proj_dioph none)
      (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.proj_dioph none))
      (fun i => Dioph.proj_dioph _)
  have dmid : Dioph {u : Fin2 (n + 4) → ℕ | ∀ x < u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))),
      Option.elim' x u ∈ S} := forall_lt_dioph dS (Dioph.proj_dioph _)
  have dfirst : Dioph {u : Fin2 (n + 4) → ℕ |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) 0
        = F (fun i => u (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))))} :=
    Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.const_dioph 0))
      (Dioph.reindex_diophFn (fun i => Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))) dF)
  have dlast : Dioph {u : Fin2 (n + 4) → ℕ |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) (u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))))
        = u (Fin2.fs (Fin2.fs Fin2.fz))} :=
    Dioph.eq_dioph (beta_dioph (Dioph.proj_dioph _) (Dioph.proj_dioph _) (Dioph.proj_dioph _))
      (Dioph.proj_dioph _)
  have dS2 : Dioph ({u : Vector3 ℕ (n + 4) |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) 0
        = F (fun i => u (Fin2.fs (Fin2.fs (Fin2.fs (Fin2.fs i)))))} ∩
    ({u : Vector3 ℕ (n + 4) | ∀ x < u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))),
      Option.elim' x u ∈ S} ∩
    {u : Vector3 ℕ (n + 4) |
      beta (u (Fin2.fs Fin2.fz)) (u Fin2.fz) (u (Fin2.fs (Fin2.fs (Fin2.fs Fin2.fz))))
        = u (Fin2.fs (Fin2.fs Fin2.fz))})) := dfirst.inter (dmid.inter dlast)
  rw [Dioph.diophFn_vec]
  refine Dioph.ext (Dioph.vec_ex1_dioph _ (Dioph.vec_ex1_dioph _ dS2)) fun v => ?_
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hS, Vector3.cons_fz, Vector3.cons_fs,
    Option.elim']
  rw [precFn_iff]
  rfl

/-! ### From `List.Vector` to `Vector3` -/

/-- Convert an inductively indexed vector to a `List.Vector`. -/
def toLV {n : ℕ} (v : Vector3 ℕ n) : List.Vector ℕ n :=
  List.Vector.ofFn (fun i : Fin n => v (Fin2.ofFin i))

@[simp] theorem toLV_get {n : ℕ} (v : Vector3 ℕ n) (i : Fin n) :
    (toLV v).get i = v (Fin2.ofFin i) := List.Vector.get_ofFn _ _

@[simp] theorem toLV_head {n : ℕ} (v : Vector3 ℕ (n + 1)) : (toLV v).head = v Fin2.fz := by
  rw [← List.Vector.get_zero, toLV_get, Fin2.ofFin_zero]

@[simp] theorem toLV_tail {n : ℕ} (v : Vector3 ℕ (n + 1)) :
    (toLV v).tail = toLV (fun i => v (Fin2.fs i)) := by
  refine List.Vector.ext fun i => ?_
  rw [List.Vector.get_tail_succ, toLV_get, toLV_get, Fin2.ofFin_succ]

@[simp] theorem toLV_cons {n : ℕ} (x : ℕ) (v : Vector3 ℕ n) :
    toLV (Vector3.cons x v) = x ::ᵥ toLV v := by
  refine List.Vector.ext fun i => ?_
  refine Fin.cases ?_ ?_ i
  · rw [List.Vector.get_cons_zero, toLV_get, Fin2.ofFin_zero]
    rfl
  · intro j
    rw [List.Vector.get_cons_succ, toLV_get, toLV_get, Fin2.ofFin_succ]
    rfl

theorem toLV_ofFn {n : ℕ} (g : Fin n → ℕ) :
    toLV (fun i : Fin2 n => g (Fin2.toFin i)) = List.Vector.ofFn g := by
  refine List.Vector.ext fun i => ?_
  rw [toLV_get, List.Vector.get_ofFn, Fin2.toFin_ofFin]

/-- A function of `List.Vector`s is Diophantine if the corresponding function of `Vector3`s is. -/
def DiophFnV {n : ℕ} (f : List.Vector ℕ n → ℕ) : Prop :=
  DiophFn (fun v : Vector3 ℕ n => f (toLV v))

/-! ### Primitive recursive functions are Diophantine -/

theorem precFn_eq {n : ℕ} (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ)
    (w : Vector3 ℕ n) (x : ℕ) :
    precFn (fun v => f (toLV v)) (fun v => g (toLV v)) w x
      = Nat.rec (motive := fun _ => ℕ) (f (toLV w)) (fun y IH => g (y ::ᵥ IH ::ᵥ toLV w)) x := by
  induction x with
  | zero => rfl
  | succ y ih => simp [precFn, ih]

/-- Every primitive recursive function is Diophantine. -/
theorem diophFnV_of_primrec' {n : ℕ} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    DiophFnV f := by
  induction hf with
  | zero => exact Dioph.const_dioph 0
  | succ =>
      have h : DiophFn (fun v : Vector3 ℕ 1 => v Fin2.fz + 1) :=
        Dioph.add_dioph (Dioph.proj_dioph _) (Dioph.const_dioph 1)
      refine cast (congrArg DiophFn ?_) h
      funext v
      simp
  | get i =>
      have h : DiophFn (fun v : Vector3 ℕ _ => v (Fin2.ofFin i)) := Dioph.proj_dioph _
      refine cast (congrArg DiophFn ?_) h
      funext v
      simp
  | @comp m n f g _ _ hf hg =>
      have hall : VectorAllP DiophFn
          (fun (i : Fin2 n) (a : Vector3 ℕ m) => g (Fin2.toFin i) (toLV a)) :=
        (vectorAllP_iff_forall _ _).2 (fun i => hg (Fin2.toFin i))
      have h := Dioph.diophFn_comp hf
        (fun (i : Fin2 n) (a : Vector3 ℕ m) => g (Fin2.toFin i) (toLV a)) hall
      refine cast (congrArg DiophFn ?_) h
      funext a
      exact congrArg f (toLV_ofFn (fun j : Fin n => g j (toLV a)))
  | @prec n f g _ _ hf hg =>
      have h := precFn_dioph hf hg
      refine cast (congrArg DiophFn ?_) h
      funext v
      rw [precFn_eq]
      show _ = Nat.rec (motive := fun _ => ℕ) (f (toLV v).tail)
        (fun y IH => g (y ::ᵥ IH ::ᵥ (toLV v).tail)) ((toLV v).head)
      simp

/-! ### The MRDP theorem -/

/-- A recursively enumerable predicate is the domain of the evaluation of a code, hence is
described by the step-bounded evaluation function `evaln`. -/
theorem exists_code_of_rePred {p : ℕ → Prop} (hp : REPred p) :
    ∃ c : Nat.Partrec.Code, ∀ a, p a ↔ ∃ k, (Nat.Partrec.Code.evaln k c a).isSome := by
  have hpart : Nat.Partrec fun a => Part.assert (p a) fun _ => Part.some 0 :=
    Partrec.nat_iff.mp hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hpart
  refine ⟨c, fun a => ?_⟩
  constructor
  · intro ha
    have h0 : (0 : ℕ) ∈ c.eval a := by rw [hc]; simp [ha]
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h0
    exact ⟨k, by rw [Option.isSome_iff_exists]; exact ⟨0, hk⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    have hmem : x ∈ c.eval a := Nat.Partrec.Code.evaln_complete.mpr ⟨k, hx⟩
    rw [hc] at hmem
    obtain ⟨⟨h1, h2⟩, h3⟩ := hmem
    exact h1

/-- **MRDP theorem** (Matiyasevich–Robinson–Davis–Putnam): every recursively enumerable
predicate on `ℕ` is Diophantine. -/
theorem dioph_of_rePred (p : ℕ → Prop) (hp : REPred p) :
    Dioph {v : Fin2 1 → ℕ | p (v Fin2.fz)} := by
  obtain ⟨c, hc⟩ := exists_code_of_rePred hp
  set F : List.Vector ℕ 2 → ℕ :=
    fun v => ((Nat.Partrec.Code.evaln v.head c v.tail.head).map Nat.succ).getD 0 with hF
  have hprim : Primrec F := by
    have h1 : Primrec (fun v : List.Vector ℕ 2 => Nat.Partrec.Code.evaln v.head c v.tail.head) :=
      Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.vector_head
        (Primrec.const c)) (Primrec.vector_head.comp Primrec.vector_tail))
    exact Primrec.option_getD.comp (Primrec.option_map h1 (Primrec.succ.comp Primrec.snd))
      (Primrec.const 0)
  have hFd : DiophFn (fun v : Vector3 ℕ 2 => F (toLV v)) :=
    diophFnV_of_primrec' (Nat.Primrec'.of_prim hprim)
  have hS : Dioph {v : Vector3 ℕ 2 | 0 < F (toLV v)} := Dioph.lt_dioph (Dioph.const_dioph 0) hFd
  refine Dioph.ext (Dioph.vec_ex1_dioph 1 hS) fun v => ?_
  simp only [Set.mem_setOf_eq]
  rw [hc (v Fin2.fz)]
  refine exists_congr fun k => ?_
  have hval : F (toLV (Vector3.cons k v)) =
      ((Nat.Partrec.Code.evaln k c (v Fin2.fz)).map Nat.succ).getD 0 := by
    rw [hF]
    simp
  rw [hval]
  rcases h : Nat.Partrec.Code.evaln k c (v Fin2.fz) with _ | x <;> simp

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

