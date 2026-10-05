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
def gapWindow : Finset ℤ := Finset.Icc 1450 1460

/-- The candidate tuple: those integers of the window that are coprime to `210 = 2*3*5*7`. -/
def gapTuple : Finset ℤ := gapWindow.filter fun n => Int.gcd n 210 = 1

lemma gapTuple_eq : gapTuple = {1451, 1453, 1457, 1459} := by
  decide

lemma gapTuple_card : gapTuple.card = 4 := by
  rw [gapTuple_eq]; decide

lemma gapTuple_bounds : ∀ h ∈ gapTuple, (1451:ℤ) ≤ h ∧ h ≤ 1459 := by
  decide

/-- `nu H p` is the number of residue classes mod `p` occupied by the tuple `H`. -/
noncomputable def nu (H : Finset ℤ) (p : ℕ) : ℕ := (H.image (Int.cast : ℤ → ZMod p)).card

/-- A finite set of integers is *admissible* if for every prime `p` it misses at least one
residue class mod `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The local factor of the Hardy–Littlewood singular series at the prime `p`. -/
noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - (nu H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

/-- The partial product of the singular series over all primes `≤ N`. -/
noncomputable def singularPartial (H : Finset ℤ) (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, localFactor H p

/-! ## Admissibility and the number of occupied residues -/

lemma exists_missing_iff (H : Finset ℤ) (p : ℕ) [NeZero p] :
    (∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r) ↔ nu H p < p := by
  constructor
  · rintro ⟨r, hr⟩
    have hsub : (H.image (Int.cast : ℤ → ZMod p)) ⊆ Finset.univ.erase r := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, ZMod.card] at hcard
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    simp only [nu]
    omega
  · intro h
    by_contra hcon
    push_neg at hcon
    have himg : (H.image (Int.cast : ℤ → ZMod p)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro r
      obtain ⟨x, hx, hxr⟩ := hcon r
      simp only [Finset.mem_image]
      exact ⟨x, hx, hxr⟩
    simp only [nu, himg, Finset.card_univ, ZMod.card] at h
    exact lt_irrefl _ h

lemma nu_le_card (H : Finset ℤ) (p : ℕ) : nu H p ≤ H.card := by
  unfold nu
  exact Finset.card_image_le

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

lemma zero_missing {p : ℕ} (hp : p.Prime) (hp8 : p ≤ 8) : ∀ h ∈ gapTuple, (h : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h2 := hp.two_le
  have hdvd : (p : ℤ) ∣ 210 := by
    interval_cases p <;> revert hp <;> decide
  intro h hh hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hgcd : Int.gcd h 210 = 1 := by
    have := (Finset.mem_filter.mp hh).2
    simpa using this
  have hdd : (p : ℕ) ∣ Int.gcd h 210 := Int.dvd_gcd hz hdvd
  rw [hgcd] at hdd
  have := Nat.le_of_dvd one_pos hdd
  omega

lemma nu_gapTuple_lt {p : ℕ} (hp : p.Prime) : nu gapTuple p < p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases h9 : 9 ≤ p
  · rw [nu_gapTuple_eq_four h9]; omega
  · exact (exists_missing_iff gapTuple p).mp ⟨0, zero_missing hp (by omega)⟩

lemma gapTuple_admissible : Admissible gapTuple := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact (exists_missing_iff gapTuple p).mpr (nu_gapTuple_lt hp)

/-! ## Bounds on the local factors -/

lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [sub_pos, div_lt_one hp0]
  linarith

lemma localFactor_pos {p : ℕ} (hp : p.Prime) : 0 < localFactor gapTuple p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnu : (nu gapTuple p : ℝ) < (p : ℝ) := by exact_mod_cast nu_gapTuple_lt hp
  have h1 : 0 < 1 - (nu gapTuple p : ℝ) / p := by
    rw [sub_pos, div_lt_one hp0]; exact hnu
  exact div_pos h1 (pow_pos (one_sub_inv_pos hp) _)

lemma inv_le_localFactor {p : ℕ} (hp : p.Prime) : 1 / (p : ℝ) ≤ localFactor gapTuple p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnu : (nu gapTuple p : ℝ) ≤ (p : ℝ) - 1 := by
    have := nu_gapTuple_lt hp
    have : (nu gapTuple p : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast this
    linarith
  have hA : 1 / (p : ℝ) ≤ 1 - (nu gapTuple p : ℝ) / p := by
    have key : (1 - (nu gapTuple p : ℝ) / p) - 1 / p
        = ((p : ℝ) - (nu gapTuple p : ℝ) - 1) / p := by
      field_simp
    have hnn : 0 ≤ ((p : ℝ) - (nu gapTuple p : ℝ) - 1) / p :=
      div_nonneg (by linarith) hp0.le
    linarith
  have hden : 0 < (1 - 1 / (p : ℝ)) ^ 4 := pow_pos (one_sub_inv_pos hp) _
  have hden1 : (1 - 1 / (p : ℝ)) ^ 4 ≤ 1 := by
    have h1 : 1 - 1 / (p : ℝ) ≤ 1 := by
      have : 0 < 1 / (p : ℝ) := by positivity
      linarith
    exact pow_le_one₀ (le_of_lt (one_sub_inv_pos hp)) h1
  rw [localFactor, gapTuple_card, le_div_iff₀ hden]
  nlinarith [hA, hden, hden1, one_div_pos.mpr hp0]

lemma localFactor_le_one {p : ℕ} (hp : 11 ≤ p) : localFactor gapTuple p ≤ 1 := by
  have ht : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have ht0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one ht0]; linarith
  rw [localFactor, gapTuple_card, nu_gapTuple_eq_four (by omega), div_le_one (pow_pos hpos 4)]
  have hkey : (1 - 1 / (p : ℝ)) ^ 4 - (1 - 4 / (p : ℝ))
      = (6 * (p : ℝ) ^ 2 - 4 * (p : ℝ) + 1) / (p : ℝ) ^ 4 := by
    field_simp
    ring
  nlinarith [hkey, div_nonneg (by nlinarith : (0:ℝ) ≤ 6 * (p : ℝ) ^ 2 - 4 * (p : ℝ) + 1)
    (by positivity : (0:ℝ) ≤ (p : ℝ) ^ 4)]

lemma one_sub_le_localFactor {p : ℕ} (hp : 11 ≤ p) :
    1 - 9 / (p : ℝ) ^ 2 ≤ localFactor gapTuple p := by
  have ht : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have ht0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    rw [sub_pos, div_lt_one ht0]; linarith
  rw [localFactor, gapTuple_card, nu_gapTuple_eq_four (by omega), le_div_iff₀ (pow_pos hpos 4)]
  have hkey : (1 - 4 / (p : ℝ)) - (1 - 9 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ)) ^ 4
      = (3 * (p : ℝ) ^ 4 - 32 * (p : ℝ) ^ 3 + 53 * (p : ℝ) ^ 2 - 36 * (p : ℝ) + 9)
        / (p : ℝ) ^ 6 := by
    field_simp
    ring
  have hnum : (0:ℝ) ≤ 3 * (p : ℝ) ^ 4 - 32 * (p : ℝ) ^ 3 + 53 * (p : ℝ) ^ 2 - 36 * (p : ℝ) + 9 := by
    nlinarith [ht, ht0, sq_nonneg ((p:ℝ) - 11), pow_pos ht0 3, pow_pos ht0 2]
  nlinarith [hkey, div_nonneg hnum (by positivity : (0:ℝ) ≤ (p : ℝ) ^ 6)]

/-! ## Weierstrass product inequality and the tail bound -/

lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    have h0i : 0 ≤ a i := h0 i (Finset.mem_cons_self i s)
    have h1i : a i ≤ 1 := h1 i (Finset.mem_cons_self i s)
    have h0' : ∀ j ∈ s, 0 ≤ a j := fun j hj => h0 j (Finset.mem_cons_of_mem hj)
    have h1' : ∀ j ∈ s, a j ≤ 1 := fun j hj => h1 j (Finset.mem_cons_of_mem hj)
    have ihh := ih h0' h1'
    have hprod : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      Finset.prod_nonneg fun j hj => by linarith [h1' j hj]
    have hsum : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h0'
    rw [Finset.sum_cons, Finset.prod_cons]
    nlinarith [ihh, hprod, hsum, h0i, h1i]

lemma sum_inv_sq_aux (k : ℕ) :
    ∑ n ∈ Finset.Ico 11 (11 + k), (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 10 - 1 / (10 + (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : 11 ≤ 11 + k := by omega
    have hrw : 11 + (k + 1) = (11 + k) + 1 := by omega
    rw [hrw, Finset.sum_Ico_succ_top hle]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcast : ((11 + k : ℕ) : ℝ) = 11 + (k : ℝ) := by push_cast; ring
    rw [hcast]
    have hstep : (1 : ℝ) / (11 + (k : ℝ)) ^ 2
        ≤ 1 / (10 + (k : ℝ)) - 1 / (10 + ((k : ℝ) + 1)) := by
      have h1 : (0 : ℝ) < 10 + (k : ℝ) := by linarith
      have h2 : (0 : ℝ) < 11 + (k : ℝ) := by linarith
      have e : 1 / (10 + (k : ℝ)) - 1 / (10 + ((k : ℝ) + 1))
          = 1 / ((10 + (k : ℝ)) * (11 + (k : ℝ))) := by
        field_simp
        ring
      rw [e]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hcast3 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast3]
    linarith [ih, hstep]

lemma sum_inv_sq_tail (M : ℕ) : ∑ n ∈ Finset.Ico 11 M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 10 := by
  by_cases hM : M ≤ 11
  · rw [Finset.Ico_eq_empty (by omega)]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, M = 11 + k := ⟨M - 11, by omega⟩
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpos : (0 : ℝ) < 1 / (10 + (k : ℝ)) := by positivity
    linarith [sum_inv_sq_aux k]

lemma tail_prod_ge (N : ℕ) :
    (1 : ℝ) / 10 ≤ ∏ p ∈ (Finset.Ico 11 (N + 1)).filter Nat.Prime, localFactor gapTuple p := by
  set s := (Finset.Ico 11 (N + 1)).filter Nat.Prime with hs
  have hmem : ∀ p ∈ s, 11 ≤ p := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_Ico] at hp
    exact hp.1.1
  have hb : ∀ p ∈ s, (11 : ℝ) ≤ (p : ℝ) := fun p hp => by exact_mod_cast hmem p hp
  have h1 : ∏ p ∈ s, (1 - 9 / (p : ℝ) ^ 2) ≤ ∏ p ∈ s, localFactor gapTuple p := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := hb p hp
      have : (9 : ℝ) / (p : ℝ) ^ 2 ≤ 9 / 121 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [hb p hp]
      linarith
    · intro p hp
      exact one_sub_le_localFactor (hmem p hp)
  have h2 : 1 - ∑ p ∈ s, 9 / (p : ℝ) ^ 2 ≤ ∏ p ∈ s, (1 - 9 / (p : ℝ) ^ 2) := by
    refine prod_one_sub_ge s _ ?_ ?_
    · intro p hp
      have := hb p hp
      positivity
    · intro p hp
      have h := hb p hp
      rw [div_le_one (by nlinarith)]
      nlinarith
  have h3 : ∑ p ∈ s, 9 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Ico 11 (N + 1), 9 / (n : ℝ) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro n _ _
    positivity
  have h4 : ∑ n ∈ Finset.Ico 11 (N + 1), (9 : ℝ) / (n : ℝ) ^ 2 ≤ 9 / 10 := by
    have : ∑ n ∈ Finset.Ico 11 (N + 1), (9 : ℝ) / (n : ℝ) ^ 2
        = 9 * ∑ n ∈ Finset.Ico 11 (N + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [this]
    linarith [sum_inv_sq_tail (N + 1)]
  linarith

/-! ## The partial products -/

lemma primes_lt_eleven {p : ℕ} (hp : p.Prime) (h : p < 11) : p ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  have h2 := hp.two_le
  interval_cases p <;> revert hp <;> decide

lemma small_prod_ge (s : Finset ℕ) (hs : s ⊆ ({2, 3, 5, 7} : Finset ℕ)) :
    (1 : ℝ) / 210 ≤ ∏ p ∈ s, localFactor gapTuple p := by
  have hprime : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    have := hs hp
    fin_cases this <;> norm_num
  have h1 : ∏ p ∈ s, (1 : ℝ) / (p : ℝ) ≤ ∏ p ∈ s, localFactor gapTuple p := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := (hprime p hp).two_le
      have : (0:ℝ) < (p:ℝ) := by
        have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hprime p hp).two_le
        linarith
      positivity
    · intro p hp
      exact inv_le_localFactor (hprime p hp)
  have hdvd : (∏ p ∈ s, p) ∣ (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ hs
  have hval : (∏ p ∈ ({2, 3, 5, 7} : Finset ℕ), p) = 210 := by decide
  rw [hval] at hdvd
  have hple : (∏ p ∈ s, p) ≤ 210 := Nat.le_of_dvd (by norm_num) hdvd
  have hppos : 0 < ∏ p ∈ s, p := by
    refine Finset.prod_pos fun p hp => ?_
    exact (hprime p hp).pos
  have h2 : (1 : ℝ) / 210 ≤ ∏ p ∈ s, (1 : ℝ) / (p : ℝ) := by
    have hcast : ∏ p ∈ s, (1 : ℝ) / (p : ℝ) = 1 / ((∏ p ∈ s, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      rw [Finset.prod_div_distrib]
      simp
    rw [hcast]
    have h1' : (0:ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by exact_mod_cast hppos
    have h2' : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ 210 := by exact_mod_cast hple
    exact one_div_le_one_div_of_le h1' h2'
  linarith

lemma singularPartial_succ (H : Finset ℤ) (N : ℕ) :
    singularPartial H (N + 1) =
      singularPartial H N * (if (N + 1).Prime then localFactor H (N + 1) else 1) := by
  simp only [singularPartial, Finset.prod_filter]
  rw [Finset.prod_range_succ]

lemma singularPartial_pos (N : ℕ) : 0 < singularPartial gapTuple N := by
  refine Finset.prod_pos fun p hp => ?_
  exact localFactor_pos (Finset.mem_filter.mp hp).2

lemma singularPartial_ge (N : ℕ) : (1 : ℝ) / 2100 ≤ singularPartial gapTuple N := by
  by_cases hN : N + 1 ≤ 11
  · have hsub : (Finset.range (N + 1)).filter Nat.Prime ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact primes_lt_eleven hp.2 (by omega)
    have hbound := small_prod_ge _ hsub
    simp only [singularPartial]
    linarith
  · push_neg at hN
    have hsplit : singularPartial gapTuple N
        = (∏ p ∈ (Finset.range 11).filter Nat.Prime, localFactor gapTuple p)
          * ∏ p ∈ (Finset.Ico 11 (N + 1)).filter Nat.Prime, localFactor gapTuple p := by
      simp only [singularPartial, Finset.prod_filter, Finset.range_eq_Ico]
      rw [Finset.prod_Ico_consecutive _ (by omega : 0 ≤ 11) (by omega : 11 ≤ N + 1)]
    have hsub : (Finset.range 11).filter Nat.Prime ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact primes_lt_eleven hp.2 hp.1
    have hA := small_prod_ge _ hsub
    have hB := tail_prod_ge N
    rw [hsplit]
    nlinarith [hA, hB]

lemma singularPartial_antitone :
    Antitone fun N => singularPartial gapTuple (N + 10) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have hstep : singularPartial gapTuple (n + 10 + 1)
      = singularPartial gapTuple (n + 10)
        * (if (n + 10 + 1).Prime then localFactor gapTuple (n + 10 + 1) else 1) :=
    singularPartial_succ _ _
  have hpos := singularPartial_pos (n + 10)
  have hle : (if (n + 10 + 1).Prime then localFactor gapTuple (n + 10 + 1) else 1) ≤ 1 := by
    split_ifs with h
    · exact localFactor_le_one (by omega)
    · exact le_refl 1
  have hidx : n + 1 + 10 = n + 10 + 1 := by omega
  show singularPartial gapTuple (n + 1 + 10) ≤ singularPartial gapTuple (n + 10)
  rw [hidx, hstep]
  nlinarith [hpos, hle]

lemma singularPartial_tendsto :
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (singularPartial gapTuple) Filter.atTop (nhds L) := by
  have hanti := singularPartial_antitone
  have hbdd : BddBelow (Set.range fun N => singularPartial gapTuple (N + 10)) := by
    refine ⟨1 / 2100, ?_⟩
    rintro x ⟨N, rfl⟩
    exact singularPartial_ge _
  have h := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ N, singularPartial gapTuple (N + 10), ?_, ?_⟩
  · have : (1:ℝ) / 2100 ≤ ⨅ N, singularPartial gapTuple (N + 10) :=
      le_ciInf fun N => singularPartial_ge _
    linarith
  · exact (Filter.tendsto_add_atTop_iff_nat 10).mp h

/-! ## Minimality of the diameter -/

/-- No admissible 4-tuple fits into a window of seven consecutive integers: the diameter `8`
realised by `gapTuple` is the least possible one for an admissible 4-tuple. -/
lemma no_admissible_four_short (K : Finset ℤ) (c : ℤ)
    (hsub : K ⊆ Finset.Icc c (c + 6)) (hcard : K.card = 4) : ¬ Admissible K := by
  intro hadm
  obtain ⟨r2, hr2⟩ := hadm 2 Nat.prime_two
  have hsame : ∀ h₁ ∈ K, ∀ h₂ ∈ K, (2:ℤ) ∣ (h₁ - h₂) := by
    intro h₁ hh₁ h₂ hh₂
    have d : ∀ z x y : ZMod 2, x ≠ z → y ≠ z → x = y := by decide
    have e : ((h₁ : ℤ) : ZMod 2) = ((h₂ : ℤ) : ZMod 2) := d r2 _ _ (hr2 _ hh₁) (hr2 _ hh₂)
    have hmod := (ZMod.intCast_eq_intCast_iff h₁ h₂ 2).mp e
    have := Int.ModEq.dvd hmod.symm
    exact_mod_cast this
  by_cases hall : ∀ h ∈ K, (2:ℤ) ∣ (h - c)
  · have hsubT : K ⊆ Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ) := by
      intro h hh
      have hb := Finset.mem_Icc.mp (hsub hh)
      have hd := hall h hh
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h - c, by omega, by ring⟩
    have hTcard : (Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ)).card = 4 := by
      rw [Finset.card_image_of_injective _ (add_right_injective c)]
      decide
    have hKT : K = Finset.image (fun j => c + j) ({0, 2, 4, 6} : Finset ℤ) :=
      Finset.eq_of_subset_of_card_le hsubT (by rw [hTcard, hcard])
    obtain ⟨r3, hr3⟩ := hadm 3 (by norm_num)
    have hex : ∀ x : ZMod 3, ∃ j ∈ ({0, 2, 4, 6} : Finset ℤ), ((c + j : ℤ) : ZMod 3) = x := by
      intro x
      have h3 : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
      rcases h3 (x - ((c : ℤ) : ZMod 3)) with h | h | h
      · refine ⟨0, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) := by linear_combination h
        push_cast
        rw [hx]; ring
      · refine ⟨4, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) + 1 := by linear_combination h
        have h4 : (4 : ZMod 3) = 1 := by decide
        push_cast
        rw [hx, h4]
      · refine ⟨2, by decide, ?_⟩
        have hx : x = ((c : ℤ) : ZMod 3) + 2 := by linear_combination h
        push_cast
        rw [hx]
    obtain ⟨j, hj, hjx⟩ := hex r3
    have hmem : (c + j) ∈ K := by
      rw [hKT]; exact Finset.mem_image_of_mem _ hj
    exact hr3 _ hmem hjx
  · push_neg at hall
    obtain ⟨h₀, hh₀, hodd⟩ := hall
    have hsub3 : K ⊆ Finset.image (fun j => c + j) ({1, 3, 5} : Finset ℤ) := by
      intro h hh
      have hb := Finset.mem_Icc.mp (hsub hh)
      have hd := hsame h hh h₀ hh₀
      have hb0 := Finset.mem_Icc.mp (hsub hh₀)
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h - c, by omega, by ring⟩
    have hle := Finset.card_le_card hsub3
    have h3 : (Finset.image (fun j => c + j) ({1, 3, 5} : Finset ℤ)).card ≤ 3 :=
      le_trans Finset.card_image_le (by decide)
    omega

/-! ## Main theorem -/

/-- **Singular series gaps, window `[1450, 1460]`.**
The four integers of the range `1450 … 1460` that are coprime to `210` form an admissible
4-tuple of diameter `8` (the least possible diameter for an admissible 4-tuple), and the
associated Hardy–Littlewood singular series has strictly positive partial products which
converge to a strictly positive limit. -/
theorem SingularSeriesGaps14501460 :
    gapTuple = {1451, 1453, 1457, 1459} ∧
    gapTuple.card = 4 ∧
    (∀ h ∈ gapTuple, (1450 : ℤ) ≤ h ∧ h ≤ 1460) ∧
    (∀ a ∈ gapTuple, ∀ b ∈ gapTuple, b - a ≤ 8) ∧
    (∃ a ∈ gapTuple, ∃ b ∈ gapTuple, b - a = 8) ∧
    Admissible gapTuple ∧
    (∀ N, 0 < singularPartial gapTuple N) ∧
    (∀ N, (1 : ℝ) / 2100 ≤ singularPartial gapTuple N) ∧
    (∀ (K : Finset ℤ) (c : ℤ), K ⊆ Finset.Icc c (c + 6) → K.card = 4 → ¬ Admissible K) ∧
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (singularPartial gapTuple) Filter.atTop (nhds L) := by
  refine ⟨gapTuple_eq, gapTuple_card, ?_, ?_, ?_, gapTuple_admissible, singularPartial_pos,
    singularPartial_ge, no_admissible_four_short, singularPartial_tendsto⟩
  · intro h hh
    obtain ⟨h1, h2⟩ := gapTuple_bounds h hh
    omega
  · intro a ha b hb
    obtain ⟨-, h2⟩ := gapTuple_bounds b hb
    obtain ⟨h3, -⟩ := gapTuple_bounds a ha
    omega
  · exact ⟨1451, by rw [gapTuple_eq]; decide, 1459, by rw [gapTuple_eq]; decide, by norm_num⟩

end Brockian

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

