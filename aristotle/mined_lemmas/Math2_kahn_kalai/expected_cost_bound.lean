import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

theorem expected_cost_bound (H : Finset (Finset α)) (ℓ h : ℕ)
    (hb : ∀ S ∈ H, S.card ≤ ℓ) (hle : ℓ ≤ 2 * h + 1)
    (p : ℝ) (hp : 0 < p) (hq1 : 64 * p ≤ 1) :
    ∑ W : Finset α, weight (64 * p) W * cost p (Ufam H h W) ≤ (1 / 32) * (1 / 16) ^ h := by
  classical
  set q : ℝ := 64 * p with hqdef
  have hq0 : 0 < q := by positivity
  have hwnn : ∀ W : Finset α, 0 ≤ weight q W := weight_nonneg hq0.le hq1
  set P : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun x => x.2 ∈ Ufam H h x.1) with hPdef
  set Q : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun y => (∃ S ∈ H, S ⊆ y.1) ∧ y.2 ⊆ edgeIn H y.1) with hQdef
  -- Step 0: rewrite the sum as a sum over pairs.
  have step1 : ∑ W : Finset α, weight q W * cost p (Ufam H h W)
      = ∑ x ∈ P, weight q x.1 * p ^ x.2.card := by
    rw [hPdef, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun W _ => ?_
    show weight q W * cost p (Ufam H h W)
        = ∑ T : Finset α, if T ∈ Ufam H h W then weight q W * p ^ T.card else 0
    rw [Finset.sum_ite_mem, Finset.univ_inter, cost, Finset.mul_sum]
  -- Step 1: the pointwise weight bound.
  have pointwise : ∀ x ∈ P,
      weight q x.1 * p ^ x.2.card ≤ (1 / 64 : ℝ) ^ (h + 1) * weight q (x.1 ∪ x.2) := by
    rintro ⟨W, T⟩ hx
    simp only [hPdef, Finset.mem_filter] at hx
    have hT : T ∈ Ufam H h W := hx.2
    have hd : Disjoint T W := Ufam_disjoint hT
    have hm : h + 1 ≤ T.card := Ufam_card_gt T hT
    have hid : weight q W * q ^ T.card = weight q (W ∪ T) * (1 - q) ^ T.card :=
      weight_union_disjoint q hd
    have hqpow : (0:ℝ) < q ^ T.card := pow_pos hq0 _
    rw [← mul_le_mul_iff_of_pos_right hqpow]
    have hlhs : weight q W * p ^ T.card * q ^ T.card
        = weight q (W ∪ T) * (1 - q) ^ T.card * p ^ T.card := by
      rw [show weight q W * p ^ T.card * q ^ T.card
            = (weight q W * q ^ T.card) * p ^ T.card by ring, hid]
    rw [hlhs]
    have hqp : q ^ T.card = 64 ^ T.card * p ^ T.card := by
      rw [hqdef, mul_pow]
    rw [hqp]
    have h1 : (1 - q) ^ T.card ≤ 1 := by
      apply pow_le_one₀ (by linarith) (by linarith)
    have h2 : (1:ℝ) ≤ (1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card := by
      have hstep : (1 / 64 : ℝ) ^ T.card ≤ (1 / 64 : ℝ) ^ (h + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      have : (1 / 64 : ℝ) ^ T.card * 64 ^ T.card = 1 := by
        rw [← mul_pow]; norm_num
      nlinarith [pow_pos (show (0:ℝ) < 64 by norm_num) T.card]
    have hppos : (0:ℝ) < p ^ T.card := pow_pos hp _
    have hwn := hwnn (W ∪ T)
    calc weight q (W ∪ T) * (1 - q) ^ T.card * p ^ T.card
        ≤ weight q (W ∪ T) * 1 * p ^ T.card := by
          apply mul_le_mul_of_nonneg_right _ hppos.le
          exact mul_le_mul_of_nonneg_left h1 hwn
      _ ≤ (1 / 64 : ℝ) ^ (h + 1) * weight q (W ∪ T) * (64 ^ T.card * p ^ T.card) := by
          have : weight q (W ∪ T) * 1 * p ^ T.card
              = weight q (W ∪ T) * p ^ T.card := by ring
          rw [this]
          have hgoal : weight q (W ∪ T) * p ^ T.card
              ≤ weight q (W ∪ T) * ((1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card) * p ^ T.card := by
            apply mul_le_mul_of_nonneg_right _ hppos.le
            nlinarith
          calc weight q (W ∪ T) * p ^ T.card
              ≤ weight q (W ∪ T) * ((1 / 64 : ℝ) ^ (h + 1) * 64 ^ T.card) * p ^ T.card := hgoal
            _ = (1 / 64 : ℝ) ^ (h + 1) * weight q (W ∪ T) * (64 ^ T.card * p ^ T.card) := by ring
  -- Step 2: the injection `(W,T) ↦ (W ∪ T, T)`.
  have hmaps : ∀ x ∈ P, ((x.1 ∪ x.2, x.2) : Finset α × Finset α) ∈ Q := by
    rintro ⟨W, T⟩ hx
    simp only [hPdef, Finset.mem_filter] at hx
    have hT : T ∈ Ufam H h W := hx.2
    simp only [hQdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Ufam_exists_edge hT, Ufam_subset_edgeIn hT⟩
  have hinj : ∀ x ∈ P, ∀ y ∈ P,
      ((x.1 ∪ x.2, x.2) : Finset α × Finset α) = (y.1 ∪ y.2, y.2) → x = y := by
    rintro ⟨W, T⟩ hx ⟨W', T'⟩ hy heq
    simp only [hPdef, Finset.mem_filter] at hx hy
    have hd : Disjoint T W := Ufam_disjoint hx.2
    have hd' : Disjoint T' W' := Ufam_disjoint hy.2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h2
    have hW : W = (W ∪ T) \ T := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hyW; exact ⟨Or.inl hyW, fun hyT => (Finset.disjoint_left.1 hd) hyT hyW⟩
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact hy1
        · exact absurd hy1 hy2
    have hW' : W' = (W' ∪ T) \ T := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hyW; exact ⟨Or.inl hyW, fun hyT => (Finset.disjoint_left.1 hd') hyT hyW⟩
      · rintro ⟨hy1 | hy1, hy2⟩
        · exact hy1
        · exact absurd hy1 hy2
    have : W = W' := by rw [hW, hW', h1]
    simp [this]
  have step2 : ∑ x ∈ P, weight q (x.1 ∪ x.2) ≤ ∑ y ∈ Q, weight q y.1 := by
    have himg : ∑ x ∈ P, weight q (x.1 ∪ x.2)
        = ∑ y ∈ P.image (fun x : Finset α × Finset α => (x.1 ∪ x.2, x.2)), weight q y.1 := by
      rw [Finset.sum_image hinj]
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => hwnn y.1)
    intro y hy
    obtain ⟨x, hxP, hxy⟩ := Finset.mem_image.1 hy
    exact hxy ▸ hmaps x hxP
  -- Step 3: bounding the sum over `Q`.
  have step3 : ∑ y ∈ Q, weight q y.1 ≤ 2 ^ ℓ := by
    have hQ : ∑ y ∈ Q, weight q y.1
        = ∑ Z : Finset α, ((Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) * weight q Z := by
      rw [hQdef, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Z _ => ?_
      show (∑ T : Finset α, if (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z then weight q Z else 0) = _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hQ]
    have hbound : ∀ Z : Finset α,
        ((Finset.univ.filter
          (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) ≤ 2 ^ ℓ := by
      intro Z
      by_cases hex : ∃ S ∈ H, S ⊆ Z
      · have hset : (Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z))
              = (edgeIn H Z).powerset := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
          exact ⟨fun hT => hT.2, fun hT => ⟨hex, hT⟩⟩
        rw [hset, Finset.card_powerset]
        have : (edgeIn H Z).card ≤ ℓ := hb _ (edgeIn_mem H hex)
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) this
      · have hset : (Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)) = ∅ := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          exact fun hT => absurd hT hex
        rw [hset]
        simp
    calc ∑ Z : Finset α, ((Finset.univ.filter
            (fun T : Finset α => (∃ S ∈ H, S ⊆ Z) ∧ T ⊆ edgeIn H Z)).card : ℝ) * weight q Z
        ≤ ∑ Z : Finset α, (2 ^ ℓ : ℝ) * weight q Z := by
          refine Finset.sum_le_sum fun Z _ => ?_
          exact mul_le_mul_of_nonneg_right (hbound Z) (hwnn Z)
      _ = 2 ^ ℓ := by rw [← Finset.mul_sum, sum_weight]; ring
  -- Combine.
  rw [step1]
  have final : ∑ x ∈ P, weight q x.1 * p ^ x.2.card
      ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := by
    calc ∑ x ∈ P, weight q x.1 * p ^ x.2.card
        ≤ ∑ x ∈ P, (1 / 64 : ℝ) ^ (h + 1) * weight q (x.1 ∪ x.2) :=
          Finset.sum_le_sum pointwise
      _ = (1 / 64 : ℝ) ^ (h + 1) * ∑ x ∈ P, weight q (x.1 ∪ x.2) := by rw [Finset.mul_sum]
      _ ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := by
          apply mul_le_mul_of_nonneg_left step2 (by positivity)
  have hnum : (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ ≤ (1 / 32) * (1 / 16) ^ h := by
    have h2l : (2:ℝ) ^ ℓ ≤ 2 ^ (2 * h + 1) := by
      apply pow_le_pow_right₀ (by norm_num) hle
    have hcalc : (1 / 64 : ℝ) ^ (h + 1) * 2 ^ (2 * h + 1) = (1 / 32) * (1 / 16) ^ h := by
      rw [pow_succ, pow_succ, pow_mul]
      rw [show ((2:ℝ) ^ 2) = 4 by norm_num]
      rw [show (1 / 64 : ℝ) ^ h * (1/64) * (4 ^ h * 2) = ((1/64 : ℝ) * 4) ^ h * (1/32) by
        rw [mul_pow]; ring]
      rw [show (1 / 64 : ℝ) * 4 = 1 / 16 by norm_num]
      ring
    calc (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ
        ≤ (1 / 64 : ℝ) ^ (h + 1) * 2 ^ (2 * h + 1) := by
          apply mul_le_mul_of_nonneg_left h2l (by positivity)
      _ = (1 / 32) * (1 / 16) ^ h := hcalc
  calc ∑ x ∈ P, weight q x.1 * p ^ x.2.card
      ≤ (1 / 64 : ℝ) ^ (h + 1) * ∑ y ∈ Q, weight q y.1 := final
    _ ≤ (1 / 64 : ℝ) ^ (h + 1) * 2 ^ ℓ := by
        apply mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ (1 / 32) * (1 / 16) ^ h := hnum

end Math2

import Mathlib
import RequestProject.KahnKalai.Measure

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Covers, costs, smallness, and the *minimum fragments* of Park–Pham.
-/

open Finset

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- `G` covers `H`, i.e. `H ⊆ ⟨G⟩`: every edge of `H` contains an edge of `G`. -/
