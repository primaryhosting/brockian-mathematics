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

/-
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

lemma double_sum_bound {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b m : ℕ) :
    ∑ W : Finset α, ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U) ≤ 2 ^ l := by
  classical
  set D : Finset (Finset α × Finset α) :=
    (Finset.univ : Finset (Finset α × Finset α)).filter
      (fun z => z.2 ∈ Ucov H b z.1 ∧ z.2.card = m) with hD
  set E : Finset (Finset α × Finset α) :=
    (Finset.univ : Finset (Finset α × Finset α)).filter (fun z => z.2 ⊆ pick H z.1) with hE
  have hDsum : ∑ W : Finset α, ∑ U ∈ (Ucov H b W).filter (fun U => U.card = m), nu r (W ∪ U)
      = ∑ z ∈ D, nu r (z.1 ∪ z.2) := by
    rw [hD, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun W _ => ?_
    dsimp only
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun U _ => rfl)
    ext U
    simp [Finset.mem_filter]
  -- the injection
  have hinj : Set.InjOn (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)) D := by
    intro z hz z' hz' heq
    simp only [Prod.mk.injEq] at heq
    have h2 : z.2 = z'.2 := heq.2
    have hdz : Disjoint z.1 z.2 := by
      rw [hD, Finset.mem_coe, Finset.mem_filter] at hz
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz.2.1
      rw [← hSe]
      exact frag_disjoint (Finset.mem_filter.mp hS).1 z.1
    have hdz' : Disjoint z'.1 z'.2 := by
      rw [hD, Finset.mem_coe, Finset.mem_filter] at hz'
      obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz'.2.1
      rw [← hSe]
      exact frag_disjoint (Finset.mem_filter.mp hS).1 z'.1
    have h1 : z.1 = z'.1 := by
      have e1 : (z.1 ∪ z.2) \ z.2 = z.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint hdz
      have e2 : (z'.1 ∪ z'.2) \ z'.2 = z'.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint hdz'
      rw [← e1, ← e2, heq.1, h2]
    exact Prod.ext h1 h2
  have himage : D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)) ⊆ E := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [hD, Finset.mem_filter] at hz
    obtain ⟨S, hS, hSe⟩ := Finset.mem_image.mp hz.2.1
    have hSH : S ∈ H := (Finset.mem_filter.mp hS).1
    have hcap : ∃ S' ∈ H, S' ⊆ z.1 ∪ z.2 := by
      rw [← hSe]; exact frag_capture hSH z.1
    have hpick := pick_spec hcap
    have hsub : pick H (z.1 ∪ z.2) ⊆ z.1 ∪ frag H S z.1 := by
      rw [hSe]; exact hpick.2
    have hfin : frag H S z.1 ⊆ pick H (z.1 ∪ z.2) := frag_subset_of_edge hSH z.1 hpick.1 hsub
    rw [hSe] at hfin
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfin⟩
  have hstep1 : ∑ z ∈ D, nu r (z.1 ∪ z.2)
      = ∑ w ∈ D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)), nu r w.1 := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  have hstep2 : ∑ w ∈ D.image (fun z : Finset α × Finset α => (z.1 ∪ z.2, z.2)), nu r w.1
      ≤ ∑ w ∈ E, nu r w.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg himage (fun w _ _ => nu_nonneg hr0 hr1 w.1)
  have hstep3 : ∑ w ∈ E, nu r w.1 ≤ 2 ^ l := by
    have hEsum : ∑ w ∈ E, nu r w.1
        = ∑ Z : Finset α, nu r Z * ((2 : ℝ) ^ (pick H Z).card) := by
      rw [hE, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun Z _ => ?_
      dsimp only
      rw [← Finset.sum_filter]
      have hset : (Finset.univ.filter (fun U : Finset α => U ⊆ pick H Z))
          = (pick H Z).powerset := by
        ext U; simp
      rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]
      push_cast
      ring
    rw [hEsum]
    calc ∑ Z : Finset α, nu r Z * ((2 : ℝ) ^ (pick H Z).card)
        ≤ ∑ Z : Finset α, nu r Z * (2 ^ l : ℝ) := by
          refine Finset.sum_le_sum fun Z _ => ?_
          have h1 : ((2 : ℝ) ^ (pick H Z).card) ≤ (2 ^ l : ℝ) := by
            exact pow_le_pow_right₀ (by norm_num) (card_pick_le hH Z)
          exact mul_le_mul_of_nonneg_left h1 (nu_nonneg hr0 hr1 Z)
      _ = 2 ^ l := by rw [← Finset.sum_mul, sum_nu, one_mul]
  rw [hDsum, hstep1]
  linarith [hstep2, hstep3]

/-- For each fragment size `m`, the expected contribution to the cost is at most
`2 ^ l * (q / r) ^ m`. -/
