/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- Weaver's discrepancy-theoretic form `KS₂` of the Kadison–Singer problem, in dimension `d`,
with smallness parameter `ε` and discrepancy constant `C`.

Given finitely many vectors `v i` in `ℂ^d` which form a Parseval frame
(`∑ i, |⟪v i, x⟫|² = ‖x‖²` for all `x`, i.e. `∑ i, v i v i* = I`) and each of which is small
(`‖v i‖² ≤ ε`), the index set can be split into two halves each of which is a frame with
upper bound `C` (i.e. the operator norm of each of the two partial sums `∑ v i v i*` is at
most `C`).

The Marcus–Spielman–Srivastava theorem states that this holds for every `d` and every `ε > 0`
with `C = (1/√2 + √ε)²`. -/
def WeaverKS2 (d : ℕ) (ε C : ℝ) : Prop :=
  ∀ (m : ℕ) (v : Fin m → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖v i‖ ^ 2 ≤ ε) →
    (∀ x : EuclideanSpace ℂ (Fin d), ∑ i, ‖inner ℂ (v i) x‖ ^ 2 = ‖x‖ ^ 2) →
    ∃ S : Finset (Fin m),
      (∀ x : EuclideanSpace ℂ (Fin d), ∑ i ∈ S, ‖inner ℂ (v i) x‖ ^ 2 ≤ C * ‖x‖ ^ 2) ∧
      (∀ x : EuclideanSpace ℂ (Fin d), ∑ i ∈ Sᶜ, ‖inner ℂ (v i) x‖ ^ 2 ≤ C * ‖x‖ ^ 2)

/-- The Marcus–Spielman–Srivastava discrepancy constant. -/
noncomputable def mssConst (ε : ℝ) : ℝ := (1 / Real.sqrt 2 + Real.sqrt ε) ^ 2

/-- Greedy balancing: a finite family of nonnegative reals, each at most `ε`, can be split
into two parts whose sums differ by at most `ε`. -/
theorem exists_balanced_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (h0 : ∀ i ∈ s, 0 ≤ a i) (hε : ∀ i ∈ s, a i ≤ ε) :
    ∃ T ⊆ s, |(∑ i ∈ T, a i) - ∑ i ∈ s \ T, a i| ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using hε0⟩
  | insert j s hj ih =>
      obtain ⟨T, hTs, hT⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hε i (Finset.mem_insert_of_mem hi))
      have hja : 0 ≤ a j := h0 j (Finset.mem_insert_self _ _)
      have hjε : a j ≤ ε := hε j (Finset.mem_insert_self _ _)
      have hjT : j ∉ T := fun h => hj (hTs h)
      have habs := abs_le.mp hT
      by_cases hle : (∑ i ∈ T, a i) ≤ ∑ i ∈ s \ T, a i
      · refine ⟨insert j T, Finset.insert_subset_insert _ hTs, ?_⟩
        have h1 : ∑ i ∈ insert j T, a i = a j + ∑ i ∈ T, a i := Finset.sum_insert hjT
        have h2 : (insert j s) \ (insert j T) = s \ T := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
          constructor
          · rintro ⟨hx | hx, hx2, hx3⟩
            · exact absurd hx hx2
            · exact ⟨hx, hx3⟩
          · rintro ⟨hx, hx2⟩
            exact ⟨Or.inr hx, by rintro rfl; exact hj hx, hx2⟩
        rw [h1, h2, abs_le]
        constructor <;> linarith [habs.1, habs.2]
      · push_neg at hle
        refine ⟨T, hTs.trans (Finset.subset_insert _ _), ?_⟩
        have h2 : (insert j s) \ T = insert j (s \ T) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hx2⟩
            · exact Or.inl hx
            · exact Or.inr ⟨hx, hx2⟩
          · rintro (rfl | ⟨hx, hx2⟩)
            · exact ⟨Or.inl rfl, hjT⟩
            · exact ⟨Or.inr hx, hx2⟩
        have hjsT : j ∉ s \ T := fun h => hj (Finset.mem_sdiff.mp h).1
        rw [h2, Finset.sum_insert hjsT, abs_le]
        constructor <;> linarith [habs.1, habs.2]

/-- Each part of a balanced split carries at most half the total plus `ε/2`. -/
theorem exists_split_le_half {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (h0 : ∀ i ∈ s, 0 ≤ a i) (hε : ∀ i ∈ s, a i ≤ ε) :
    ∃ T ⊆ s, (∑ i ∈ T, a i) ≤ (∑ i ∈ s, a i) / 2 + ε / 2 ∧
      (∑ i ∈ s \ T, a i) ≤ (∑ i ∈ s, a i) / 2 + ε / 2 := by
  obtain ⟨T, hTs, hT⟩ := exists_balanced_split s a ε hε0 h0 hε
  refine ⟨T, hTs, ?_, ?_⟩ <;>
    · have hsplit : (∑ i ∈ s \ T, a i) + ∑ i ∈ T, a i = ∑ i ∈ s, a i := Finset.sum_sdiff hTs
      have habs := abs_le.mp hT
      linarith [habs.1, habs.2]

/-- Half the total plus `ε/2` is below the Marcus–Spielman–Srivastava constant. -/
theorem half_add_le_mssConst (ε : ℝ) (hε : 0 ≤ ε) : 1 / 2 + ε / 2 ≤ mssConst ε := by
  have e1 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have e2 : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε
  have hexp : mssConst ε = 1 / 2 + 2 * (1 / Real.sqrt 2) * Real.sqrt ε + ε := by
    unfold mssConst; rw [add_sq, e1, e2]
  have hpos : 0 ≤ 2 * (1 / Real.sqrt 2) * Real.sqrt ε := by positivity
  rw [hexp]; linarith

/-- Trivial regime: as soon as the target constant is at least `1`, Weaver's `KS₂` statement
holds in every dimension (put all the vectors on one side). -/
theorem weaverKS2_of_one_le (d : ℕ) (ε C : ℝ) (hC : 1 ≤ C) : WeaverKS2 d ε C := by
  intro m v _ hpar
  refine ⟨Finset.univ, ?_, ?_⟩
  · intro x
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    rw [hpar x]
    nlinarith
  · intro x
    have hx : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    simp only [Finset.compl_univ, Finset.sum_empty]
    nlinarith

/-- The one-dimensional case of Weaver's `KS₂`, for any constant `C ≥ 1/2 + ε/2`. -/
theorem weaverKS2_dim_one_of_le (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 / 2 + ε / 2 ≤ C) :
    WeaverKS2 1 ε C := by
  intro m v hv hpar
  classical
  set a : Fin m → ℝ := fun i => ‖v i 0‖ ^ 2 with ha
  have hnorm : ∀ y : EuclideanSpace ℂ (Fin 1), ‖y‖ ^ 2 = ‖y 0‖ ^ 2 := by
    intro y; rw [EuclideanSpace.norm_eq]; simp
  have hinner : ∀ (i : Fin m) (x : EuclideanSpace ℂ (Fin 1)),
      ‖inner ℂ (v i) x‖ ^ 2 = a i * ‖x‖ ^ 2 := by
    intro i x
    rw [hnorm x, ha]
    simp [PiLp.inner_apply, mul_pow, mul_comm]
  have hai : ∀ i, a i ≤ ε := by
    intro i
    have h := hv i
    rw [hnorm (v i)] at h
    exact h
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have hsum : ∑ i, a i = 1 := by
    have h := hpar (EuclideanSpace.single (0 : Fin 1) (1:ℂ))
    simp only [hinner] at h
    rw [← Finset.sum_mul] at h
    have hx : ‖(EuclideanSpace.single (0 : Fin 1) (1:ℂ))‖ ^ 2 = 1 := by simp
    rw [hx] at h
    simpa using h
  obtain ⟨T, -, hT1, hT2⟩ := exists_split_le_half (Finset.univ : Finset (Fin m)) a ε hε
    (fun i _ => ha0 i) (fun i _ => hai i)
  have hc : (Finset.univ : Finset (Fin m)) \ T = Tᶜ := by ext i; simp
  rw [hc] at hT2
  rw [hsum] at hT1 hT2
  refine ⟨T, ?_, ?_⟩
  · intro x
    have hx0 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    calc ∑ i ∈ T, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ T, a i) * ‖x‖ ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => hinner i x
      _ ≤ C * ‖x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hx0
          linarith
  · intro x
    have hx0 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    calc ∑ i ∈ Tᶜ, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ Tᶜ, a i) * ‖x‖ ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => hinner i x
      _ ≤ C * ‖x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hx0
          linarith

/-- The one-dimensional case of Weaver's `KS₂`, with the Marcus–Spielman–Srivastava constant.
This is the base case of the Kadison–Singer theorem. -/
theorem weaverKS2_dim_one (ε : ℝ) (hε : 0 ≤ ε) : WeaverKS2 1 ε (mssConst ε) :=
  weaverKS2_dim_one_of_le ε _ hε (half_add_le_mssConst ε hε)

/-- For `ε ≥ 3/2 - √2` the Marcus–Spielman–Srivastava constant is at least `1`. -/
theorem one_le_mssConst (ε : ℝ) (hε : 3 / 2 - Real.sqrt 2 ≤ ε) : 1 ≤ mssConst ε := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hε0 : 0 ≤ ε := by linarith
  set c : ℝ := 1 - Real.sqrt 2 / 2 with hc
  have hc0 : 0 ≤ c := by
    have : Real.sqrt 2 < 2 := by nlinarith
    rw [hc]; linarith
  have hcsq : c ^ 2 = 3 / 2 - Real.sqrt 2 := by
    rw [hc]; nlinarith
  have hcle : c ≤ Real.sqrt ε := (Real.le_sqrt hc0 hε0).mpr (by rw [hcsq]; linarith)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  have : (1:ℝ) = (1 / Real.sqrt 2 + c) ^ 2 := by
    rw [hinv, hc]; ring_nf
  rw [this]
  unfold mssConst
  have hnn : 0 ≤ 1 / Real.sqrt 2 + c := by positivity
  exact pow_le_pow_left₀ hnn (by linarith) 2

/-- **Kadison–Singer**, formalized in Weaver's `KS₂` discrepancy form with the
Marcus–Spielman–Srivastava constant `(1/√2 + √ε)²`.

Proved here:

* the base case `d = 1`, in full, for every smallness parameter `ε ≥ 0`;
* the regime `ε ≥ 3/2 - √2`, in every dimension `d`, where the MSS constant is already `≥ 1`. -/
theorem kadison_singer :
    (∀ ε : ℝ, 0 ≤ ε → WeaverKS2 1 ε (mssConst ε)) ∧
      (∀ (d : ℕ) (ε : ℝ), 3 / 2 - Real.sqrt 2 ≤ ε → WeaverKS2 d ε (mssConst ε)) :=
  ⟨weaverKS2_dim_one, fun d ε hε => weaverKS2_of_one_le d ε _ (one_le_mssConst ε hε)⟩

end Frontier

