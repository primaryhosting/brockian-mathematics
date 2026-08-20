/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

theorem main_induction {p r : ℝ} (hp : 0 < p) (hr : r = 324 * p) (hr1 : r ≤ 1) :
    ∀ (k m : ℕ), m < 2 ^ k → ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ m) →
      ∀ θ : ℝ, 0 ≤ θ → (∀ U : Finset (Finset α), IsCover H U → θ ≤ cost p U) →
        θ * (1 - mu (dens r k) (upset H)) ≤ ebound m := by
  have hr0 : 0 < r := by rw [hr]; linarith
  intro k
  induction k with
  | zero =>
      intro m hm H hH θ hθ0 hcov
      interval_cases m
      · -- `m = 0`: every edge is empty
        by_cases hHe : H = ∅
        · have : θ ≤ cost p (∅ : Finset (Finset α)) := by
            refine hcov ∅ ?_
            intro S hS
            rw [hHe] at hS
            exact absurd hS (Finset.notMem_empty S)
          rw [cost] at this
          simp only [Finset.sum_empty] at this
          have hθ : θ = 0 := le_antisymm this hθ0
          rw [hθ, ebound_zero]
          simp
        · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hHe
          have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hH S hS))
          have : upset H = (Finset.univ : Finset (Finset α)) := by
            ext A
            simp only [Finset.mem_univ, iff_true]
            exact mem_upset.2 ⟨S, hS, by rw [hS0]; exact Finset.empty_subset A⟩
          rw [this, mu_univ, ebound_zero]
          simp
  | succ k ih =>
      intro m hm H hH θ hθ0 hcov
      rcases Nat.eq_zero_or_pos m with hm0 | hm1
      · -- `m = 0` again
        subst hm0
        by_cases hHe : H = ∅
        · have : θ ≤ cost p (∅ : Finset (Finset α)) := by
            refine hcov ∅ ?_
            intro S hS
            rw [hHe] at hS
            exact absurd hS (Finset.notMem_empty S)
          rw [cost] at this
          simp only [Finset.sum_empty] at this
          have hθ : θ = 0 := le_antisymm this hθ0
          rw [hθ, ebound_zero]
          simp
        · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.2 hHe
          have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hH S hS))
          have : upset H = (Finset.univ : Finset (Finset α)) := by
            ext A
            simp only [Finset.mem_univ, iff_true]
            exact mem_upset.2 ⟨S, hS, by rw [hS0]; exact Finset.empty_subset A⟩
          rw [this, mu_univ, ebound_zero]
          simp
      -- the main case
      set m' : ℕ := (m - 1) / 2 with hm'
      have hm'lt : m' < 2 ^ k := by
        have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      set b : ℝ := dens r k with hb
      have hb0 : 0 ≤ b := dens_nonneg (le_of_lt hr0) hr1 k
      have hb1 : b ≤ 1 := dens_le_one hr1 k
      -- one round, for each `W`
      have hstepW : ∀ W : Finset α,
          θ * (1 - mu b (upset (Hnext H W m))) ≤ ebound m' + cost p (Ufam H W m) := by
        intro W
        set κ : ℝ := cost p (Ufam H W m) with hκ
        have hκ0 : 0 ≤ κ := cost_nonneg (le_of_lt hp) _
        set θ' : ℝ := max 0 (θ - κ) with hθ'
        have hθ'0 : 0 ≤ θ' := le_max_left _ _
        have hθ'le : θ ≤ θ' + κ := by
          rcases le_total θ κ with h | h
          · have : 0 ≤ θ' := hθ'0
            linarith
          · have : θ - κ ≤ θ' := le_max_right _ _
            linarith
        have hcov' : ∀ V : Finset (Finset α), IsCover (Hnext H W m) V → θ' ≤ cost p V := by
          intro V hV
          have h1 : θ ≤ cost p (V ∪ Ufam H W m) := hcov _ (cover_combine hV)
          have h2 : cost p (V ∪ Ufam H W m) ≤ cost p V + κ :=
            cost_union_le (le_of_lt hp) V (Ufam H W m)
          have h3 : θ - κ ≤ cost p V := by linarith
          exact max_le (cost_nonneg (le_of_lt hp) _) h3
        have hbound : ∀ T ∈ Hnext H W m, T.card ≤ m' := by
          intro T hT
          have := Hnext_card_le hT
          omega
        have hIH := ih m' hm'lt (Hnext H W m) hbound θ' hθ'0 hcov'
        have hmu0 : 0 ≤ mu b (upset (Hnext H W m)) := mu_nonneg hb0 hb1 _
        have hmu1 : mu b (upset (Hnext H W m)) ≤ 1 := mu_le_one hb0 hb1 _
        nlinarith [hIH, hθ'le, hκ0, hθ0]
      -- average over `W`
      have hsum1 : ∑ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
          ≤ ∑ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m)) := by
        refine Finset.sum_le_sum ?_
        intro W _
        exact mul_le_mul_of_nonneg_left (hstepW W) (wt_nonneg (le_of_lt hr0) hr1 W)
      have hsum2 : ∑ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m))
          = ebound m' + ∑ W : Finset α, wt r W * cost p (Ufam H W m) := by
        have : ∀ W : Finset α, wt r W * (ebound m' + cost p (Ufam H W m))
            = wt r W * ebound m' + wt r W * cost p (Ufam H W m) := by
          intro W; ring
        simp only [this]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_wt, one_mul]
      have hkey : ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (1 / 9 : ℝ) ^ m := by
        have := expected_cost_le (H := H) (m := m) hH (p := p) (r := r) (c := 18)
          hp (by norm_num) (by rw [hr]; norm_num) hr1
        calc ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (2 / 18 : ℝ) ^ m := this
          _ = (1 / 9 : ℝ) ^ m := by norm_num
      have hsum3 : ∑ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
          = θ * (1 - ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))) := by
        have : ∀ W : Finset α, wt r W * (θ * (1 - mu b (upset (Hnext H W m))))
            = θ * wt r W - θ * (wt r W * mu b (upset (Hnext H W m))) := by
          intro W; ring
        simp only [this]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_wt]
        ring
      -- the union of the fresh set `W` with a `b`-random set
      have hcapture : ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))
          ≤ mu (dens r (k + 1)) (upset H) := by
        have hexp : ∀ W : Finset α, wt r W * mu b (upset (Hnext H W m))
            = ∑ V : Finset α, wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0) := by
          intro W
          rw [mu_eq_sum_indicator, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun V _ => by ring)
        have hle : ∀ W : Finset α,
            (∑ V : Finset α, wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0))
              ≤ ∑ V : Finset α, wt r W * wt b V * (if W ∪ V ∈ upset H then (1:ℝ) else 0) := by
          intro W
          refine Finset.sum_le_sum ?_
          intro V _
          have hw : 0 ≤ wt r W * wt b V :=
            mul_nonneg (wt_nonneg (le_of_lt hr0) hr1 W) (wt_nonneg hb0 hb1 V)
          have : (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0)
              ≤ (if W ∪ V ∈ upset H then (1:ℝ) else 0) := by
            by_cases h : V ∈ upset (Hnext H W m)
            · have : W ∪ V ∈ upset H := Hnext_capture h
              simp [h, this]
            · simp [h]
              positivity
          exact mul_le_mul_of_nonneg_left this hw
        calc ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))
            = ∑ W : Finset α, ∑ V : Finset α,
                wt r W * wt b V * (if V ∈ upset (Hnext H W m) then (1:ℝ) else 0) := by
              exact Finset.sum_congr rfl (fun W _ => hexp W)
          _ ≤ ∑ W : Finset α, ∑ V : Finset α,
                wt r W * wt b V * (if W ∪ V ∈ upset H then (1:ℝ) else 0) :=
              Finset.sum_le_sum (fun W _ => hle W)
          _ = ∑ C : Finset α, wt (r + b - r * b) C * (if C ∈ upset H then (1:ℝ) else 0) :=
              union_wt r b (fun C => if C ∈ upset H then (1:ℝ) else 0)
          _ = mu (dens r (k + 1)) (upset H) := by
              rw [dens_succ, hb, mu_eq_sum_indicator]
      -- put everything together
      have hfinal : θ * (1 - mu (dens r (k + 1)) (upset H))
          ≤ θ * (1 - ∑ W : Finset α, wt r W * mu b (upset (Hnext H W m))) := by
        have := hcapture
        nlinarith [hθ0]
      have hlast : ebound m' + (1 / 9 : ℝ) ^ m ≤ ebound m := by
        have h1 : ebound m' ≤ ebound (m - 1) := ebound_mono (by omega)
        have h2 := ebound_step (m := m) hm1
        linarith
      linarith [hfinal, hsum3, hsum1, hsum2, hkey, hlast]

end KahnKalai

import RequestProject.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The universal constant -/

/-- The universal constant in the Kahn-Kalai theorem produced by this proof. -/
