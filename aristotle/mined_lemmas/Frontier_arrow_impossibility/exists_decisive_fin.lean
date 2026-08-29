import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings -/

/-- A strict linear ranking (irreflexive, transitive, total) of the alternatives `A`.
`R.rel a b` means "`a` is strictly preferred to `b`". -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c
  rel_irrefl : ∀ a : A, ¬ rel a a
  rel_total : ∀ a b : A, a ≠ b → rel a b ∨ rel b a

namespace Ranking

variable {A : Type*}


theorem exists_decisive_fin {n : ℕ} {A : Type*} {F : SWF (Fin n) A}
    (hU : Unanimity F) (hI : IIA F) {a b c : A} (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    ∃ v : Fin n, Decisive F v a c := by
  classical
  -- `Pi k` is the profile in which the voters `i < k` rank `b` first and the others rank it last.
  obtain ⟨t, ht⟩ : ∃ t : ℕ → Fin n → A → ℕ, t = fun k i x =>
      if x = b then (if i.val < k then 0 else 2) else 1 := ⟨_, rfl⟩
  obtain ⟨Pi, hPi⟩ : ∃ Pi : ℕ → Fin n → Ranking A, Pi = fun k i => scoreRanking (t k i) := ⟨_, rfl⟩
  have htb : ∀ k (i : Fin n), t k i b = (if i.val < k then 0 else 2) := by
    intro k i; simp [ht]
  have htx : ∀ k (i : Fin n) x, x ≠ b → t k i x = 1 := by intro k i x hx; simp [ht, hx]
  have htop : ∀ k (i : Fin n), i.val < k → IsTopOf b (Pi k i) := by
    intro k i hik x hx
    simp only [hPi]
    exact scoreRanking_rel (by rw [htb, htx k i x hx]; split_ifs; omega)
  have hbot : ∀ k (i : Fin n), ¬ (i.val < k) → IsBotOf b (Pi k i) := by
    intro k i hik x hx
    simp only [hPi]
    exact scoreRanking_rel (by rw [htb, htx k i x hx]; split_ifs; omega)
  have hext : ∀ k, ∀ i : Fin n, IsTopOf b (Pi k i) ∨ IsBotOf b (Pi k i) := by
    intro k i
    by_cases h : i.val < k
    · exact Or.inl (htop k i h)
    · exact Or.inr (hbot k i h)
  have hFtop_n : IsTopOf b (F (Pi n)) := fun x hx => hU _ b x (fun i => htop n i i.isLt x hx)
  have hFbot_0 : IsBotOf b (F (Pi 0)) := fun x hx => hU _ x b (fun i => hbot 0 i (by omega) x hx)
  have hex : ∃ k, IsTopOf b (F (Pi k)) := ⟨n, hFtop_n⟩
  have hk0 : ¬ IsTopOf b (F (Pi 0)) := fun h =>
    (F (Pi 0)).asymm (h a hab) (hFbot_0 a hab)
  have hne0 : Nat.find hex ≠ 0 := fun h => hk0 (h ▸ Nat.find_spec hex)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjn : j < n := by
    have h1 : Nat.find hex ≤ n := Nat.find_le hFtop_n
    omega
  have htopk : IsTopOf b (F (Pi (j + 1))) := hj ▸ Nat.find_spec hex
  have hnotj : ¬ IsTopOf b (F (Pi j)) := Nat.find_min hex (by omega)
  have hbotj : IsBotOf b (F (Pi j)) := (extremal_lemma hU hI b (Pi j) (hext j)).resolve_left hnotj
  refine ⟨⟨j, hjn⟩, ?_⟩
  intro P hP
  -- The auxiliary profile `R`: the pivotal voter ranks `a` above `b` above `c`; the earlier
  -- voters keep `b` on top, the later ones keep `b` at the bottom, and everybody else's
  -- `a`-versus-`c` comparison is copied from `P`.
  obtain ⟨s, hs⟩ : ∃ s : Fin n → A → ℕ, s = fun i x =>
      if x = b then (if i.val < j then 0 else if i.val = j then 2 else 4)
      else if x = a then (if i.val = j then 1 else if (P i).rel a c then 1 else 3)
      else if x = c then (if i.val = j then 3 else if (P i).rel a c then 3 else 1)
      else 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin n → Ranking A, R = fun i => scoreRanking (s i) := ⟨_, rfl⟩
  have hsb : ∀ i : Fin n, s i b = (if i.val < j then 0 else if i.val = j then 2 else 4) := by
    intro i; simp [hs]
  have hsa : ∀ i : Fin n,
      s i a = (if i.val = j then 1 else if (P i).rel a c then 1 else 3) := by
    intro i; simp [hs, hab]
  have hsc : ∀ i : Fin n,
      s i c = (if i.val = j then 3 else if (P i).rel a c then 3 else 1) := by
    intro i; simp [hs, hcb, Ne.symm hac]
  -- `R` and `Pi j` agree on the pair `(a, b)`.
  have hmab : ∀ i : Fin n, ((R i).rel a b ↔ (Pi j i).rel a b) := by
    intro i
    rcases lt_trichotomy i.val j with h | h | h
    · refine iff_of_false ?_ ?_
      · simp only [hR]
        exact scoreRanking_not_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_not_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb j i, htx j i a hab]; split_ifs <;> omega)
  -- `R` and `Pi (j+1)` agree on the pair `(b, c)`.
  have hmbc : ∀ i : Fin n, ((R i).rel b c ↔ (Pi (j + 1) i).rel b c) := by
    intro i
    rcases lt_trichotomy i.val j with h | h | h
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
    · refine iff_of_true ?_ ?_
      · simp only [hR]
        exact scoreRanking_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_rel (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
    · refine iff_of_false ?_ ?_
      · simp only [hR]
        exact scoreRanking_not_rel (by rw [hsc i, hsb i]; split_ifs <;> omega)
      · simp only [hPi]
        exact scoreRanking_not_rel
          (by rw [htb (j + 1) i, htx (j + 1) i c hcb]; split_ifs <;> omega)
  have hFRab : (F R).rel a b := (hI R (Pi j) a b hmab).mpr (hbotj a hab)
  have hFRbc : (F R).rel b c := (hI R (Pi (j + 1)) b c hmbc).mpr (htopk c hcb)
  have hFRac : (F R).rel a c := (F R).rel_trans hFRab hFRbc
  -- `R` and `P` agree on the pair `(a, c)`.
  have hmac : ∀ i : Fin n, ((R i).rel a c ↔ (P i).rel a c) := by
    intro i
    by_cases h : i.val = j
    · have hi : i = ⟨j, hjn⟩ := Fin.ext h
      subst hi
      refine iff_of_true ?_ hP
      simp only [hR]
      exact scoreRanking_rel (by rw [hsa, hsc]; split_ifs; omega)
    · by_cases hp : (P i).rel a c
      · refine iff_of_true ?_ hp
        simp only [hR]
        exact scoreRanking_rel (by rw [hsa i, hsc i]; split_ifs; omega)
      · refine iff_of_false ?_ hp
        simp only [hR]
        exact scoreRanking_not_rel (by rw [hsa i, hsc i]; split_ifs; omega)
  exact (hI P R a c (fun i => (hmac i).symm)).mpr hFRac

/-! ## Arrow's theorem -/

/-- **Arrow's theorem**, dictatorship form: a social welfare function on at least three
alternatives, for a finite nonempty electorate, that satisfies unanimity and independence of
irrelevant alternatives has a dictator. -/
