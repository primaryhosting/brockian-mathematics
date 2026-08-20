import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem exists_gFun (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) :
    ∃ (τ : Equiv.Perm (Fin n)) (c : ∀ i, Fin (W i (τ i))), ∀ v, gFun W τ c v = σ v := by
  classical
  choose t ht1 ht2 using gadget_witness_inl W σ hσ
  obtain ⟨τ₀, hτ₀⟩ : ∃ f : Fin n → Fin n, ∀ i, f i = (t i).1.2 := ⟨_, fun _ => rfl⟩
  have key : ∀ s : Idx W, σ (Sum.inr s) = Sum.inl s.1.2 → t s.1.1 = s := by
    intro s hsj
    have hu := hσ (σ.symm (Sum.inr s))
    rw [Equiv.apply_symm_apply] at hu
    cases hv : σ.symm (Sum.inr s) with
    | inl a =>
      rw [hv, gadget_lr] at hu
      have has : s.1.1 = a := by
        by_contra hne; rw [if_neg hne] at hu; exact absurd hu (by norm_num)
      have hσa : σ (Sum.inl a) = Sum.inr s := by rw [← hv, Equiv.apply_symm_apply]
      rw [ht1 a] at hσa
      rw [has]
      exact Sum.inr_injective hσa
    | inr s' =>
      rw [hv, gadget_rr] at hu
      have hss : s' = s := by
        by_contra hne; rw [if_neg hne] at hu; exact absurd hu (by norm_num)
      subst hss
      have h2 := σ.apply_symm_apply (Sum.inr s')
      rw [hv, hsj] at h2
      exact absurd h2 (by simp)
  have hsurj : Function.Surjective τ₀ := by
    intro j
    have hv0 := hσ (σ.symm (Sum.inl j))
    rw [Equiv.apply_symm_apply] at hv0
    cases hv : σ.symm (Sum.inl j) with
    | inl a => rw [hv, gadget_ll] at hv0; exact absurd hv0 (by norm_num)
    | inr s =>
      rw [hv, gadget_rl] at hv0
      have hs2 : s.1.2 = j := by
        by_contra hne; rw [if_neg hne] at hv0; exact absurd hv0 (by norm_num)
      have hσs : σ (Sum.inr s) = Sum.inl s.1.2 := by
        have h2 := σ.apply_symm_apply (Sum.inl j)
        rw [hv] at h2; rw [h2, hs2]
      exact ⟨s.1.1, by rw [hτ₀, key s hσs, hs2]⟩
  set τ : Equiv.Perm (Fin n) := Equiv.ofBijective τ₀ (Finite.surjective_iff_bijective.mp hsurj)
  have hτapp : ∀ i, τ i = (t i).1.2 := fun i => hτ₀ i
  have hW : ∀ i, W (t i).1.1 (t i).1.2 = W i (τ i) := by
    intro i; rw [ht2 i, hτapp i]
  refine ⟨τ, fun i => Fin.cast (hW i) (t i).2, ?_⟩
  have hti : ∀ i, t i = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) i := by
    intro i
    refine Sigma.ext (Prod.ext (ht2 i) (hτapp i).symm) ?_
    exact (Fin.heq_ext_iff (hW i)).mpr rfl
  intro v
  cases v with
  | inl i =>
    show Sum.inr _ = _
    rw [ht1 i, ← hti i]
  | inr s =>
    show (if s = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) s.1.1 then Sum.inl s.1.2
        else Sum.inr s) = σ (Sum.inr s)
    by_cases hs : s = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) s.1.1
    · rw [if_pos hs]
      rcases gadget_witness_inr W σ hσ s with h | h
      · exact h.symm
      · exfalso
        have hts : t s.1.1 = s := by rw [hti s.1.1, ← hs]
        have hcontr := ht1 s.1.1
        rw [hts, ← h] at hcontr
        exact absurd (σ.injective hcontr) (by simp)
    · rw [if_neg hs]
      rcases gadget_witness_inr W σ hσ s with h | h
      · exact absurd ((key s h).symm.trans (hti s.1.1)) hs
      · exact h.symm

