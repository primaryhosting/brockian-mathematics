import Mathlib
/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Set Cardinal Ordinal
open scoped Ordinal Cardinal

namespace Frontier

/-! ## Countable ordinals -/

/-- The set of ordinals below `a` is countable exactly when `a < ω₁`. -/

theorem Inv_limit {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hex : ∃ c, IsCofSeq l c) (ih : ∀ b < l, Inv b) : Inv l := by
  obtain ⟨hc1, hc2⟩ := cofSeq_spec hex
  have hidx : ∀ ξ, ξ < l → ξ < cofSeq l (blockIdx l ξ) := fun ξ hξ =>
    lt_cofSeq_blockIdx (hc2 ξ hξ)
  have hval : ∀ ξ, ξ < l → E l ξ = max (E (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) :=
    fun ξ hξ => E_limit_apply hl hξ (hc1 _)
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    rw [E_limit hl, limitStep, if_neg (not_lt.2 hξ)]
  · intro k
    refine Set.Finite.subset ((Set.finite_Iio (k + 1)).biUnion
      (fun m (_ : m ∈ Set.Iio (k + 1)) =>
        finite_le_of_finToOne (ih (cofSeq l m) (hc1 m)).2.1 k)) ?_
    rintro ξ ⟨h1, h2⟩
    rw [hval ξ h1] at h2
    exact Set.mem_biUnion (x := blockIdx l ξ) (Nat.lt_succ_of_le (h2 ▸ le_max_right _ _))
      ⟨hidx ξ h1, h2 ▸ le_max_left _ _⟩
  · intro b hb
    obtain ⟨N, hN⟩ := hc2 b hb
    have hfin1 : (⋃ m ∈ Set.Iio (N + 1),
        {ξ : Ordinal.{0} | ξ < cofSeq l m ∧ ξ < b ∧ E (cofSeq l m) ξ ≠ E b ξ}).Finite :=
      (Set.finite_Iio (N + 1)).biUnion
        (fun m _ => coh_pair (ih (cofSeq l m) (hc1 m)) (ih b hb))
    have hfin2 : {ξ : Ordinal.{0} | ξ < b ∧ E b ξ < N + 1}.Finite :=
      finite_lt_of_finToOne (ih b hb).2.1 (N + 1)
    refine Set.Finite.subset (hfin1.union hfin2) ?_
    rintro ξ ⟨h1, h2⟩
    have hξl : ξ < l := h1.trans hb
    have hbn : blockIdx l ξ ≤ N := blockIdx_le (h1.trans hN)
    rw [hval ξ hξl] at h2
    by_cases hcase : E (cofSeq l (blockIdx l ξ)) ξ = E b ξ
    · refine Or.inr ⟨h1, ?_⟩
      rw [hcase] at h2
      have hnle : ¬ (blockIdx l ξ ≤ E b ξ) := fun hle => h2 (max_eq_left hle)
      omega
    · exact Or.inl (Set.mem_biUnion (x := blockIdx l ξ)
        (Nat.lt_succ_of_le hbn) ⟨hidx ξ hξl, h1, hcase⟩)

/-- The invariant holds at every countable ordinal. -/
