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

theorem kahn_kalai :
    ∃ K : ℝ, 0 < K ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Finset α)),
        IsUp F → pThreshold F ≤ K * qThreshold F * Real.log (ell F) := by
  refine ⟨Kconst, Kconst_pos, ?_⟩
  intro α _ _ F hF
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos
  have hlogl : Real.log 2 ≤ Real.log (ell F) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast two_le_ell F)
  have hlogl0 : 0 < Real.log (ell F) := lt_of_lt_of_le hlog2 hlogl
  have hKl : 0 < Kconst * Real.log (ell F) := mul_pos Kconst_pos hlogl0
  have hqnn : 0 ≤ qThreshold F := qThreshold_nonneg F
  have hRHS : 0 ≤ Kconst * qThreshold F * Real.log (ell F) := by
    have : 0 ≤ Kconst * qThreshold F := mul_nonneg (le_of_lt Kconst_pos) hqnn
    positivity
  refine Real.sSup_le ?_ hRHS
  rintro p₀ ⟨hp₀0, hp₀1, hp₀mu⟩
  by_contra hcon
  push_neg at hcon
  -- choose `q` slightly above the expectation threshold
  set q : ℝ := p₀ / (Kconst * Real.log (ell F)) with hq
  have hqmul : q * (Kconst * Real.log (ell F)) = p₀ := by
    rw [hq, div_mul_cancel₀ _ (ne_of_gt hKl)]
  have hq0 : 0 < q := by
    have : 0 < p₀ := lt_of_le_of_lt hRHS hcon
    rw [hq]; positivity
  have hqbig : qThreshold F < q := by
    by_contra hle
    push_neg at hle
    have : q * (Kconst * Real.log (ell F)) ≤ qThreshold F * (Kconst * Real.log (ell F)) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hKl)
    rw [hqmul] at this
    nlinarith
  have hq1 : q ≤ 1 := by
    have h1 : Kconst * Real.log 2 = 648 := Kconst_log_two
    have h2 : (648:ℝ) ≤ Kconst * Real.log (ell F) := by nlinarith [Kconst_pos]
    rw [hq, div_le_one hKl]
    linarith
  -- `F` is not `q`-small
  have hnsF : ¬ IsSmall q F := by
    intro hsmall
    have : q ≤ qThreshold F :=
      le_csSup (qThreshold_bddAbove F) ⟨le_of_lt hq0, hq1, hsmall⟩
    linarith
  have hnsH : ¬ IsSmall q (minimalElts F) := by
    rintro ⟨U, hU, hcost⟩
    exact hnsF ⟨U, cover_of_cover_minimalElts hU, hcost⟩
  -- apply the hypergraph form
  have hmain := mu_gt_half_of_not_isSmall (α := α) (H := minimalElts F) (m := ell F)
    (two_le_ell F) (fun S hS => minimalElts_card_le hS) hq0 hnsH hp₀1
    (by rw [mul_comm Kconst q, mul_assoc, hqmul])
  have hsub : mu p₀ (upset (minimalElts F)) ≤ mu p₀ F :=
    mu_mono_subset hp₀0 hp₀1 (upset_minimalElts_subset hF)
  linarith

end Math2

/-
The key lemma of Park-Pham (in the Bernoulli setting): the cover made of the large
minimum fragments has small expected cost.
-/
import RequestProject.Fragments

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
