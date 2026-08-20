import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma comp_mem_Deg {N : ℕ} (g : Cube n → Cube N) {f : Cube N → F} {D : ℕ}
    (hg : ∀ i : Fin N, (fun x => coord F i (g x)) ∈ Deg F n 1)
    (hf : f ∈ Deg F N D) : (fun x => f (g x)) ∈ Deg F n D := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      have : (fun x => mono F S (g x)) = ∏ i ∈ S, (fun x => coord F i (g x)) := by
        funext x; simp [mono, Finset.prod_apply]
      rw [this]
      exact mem_Deg_of_le (prod_mem_Deg' S _ (fun i _ => hg i)) hS
  | zero => exact Submodule.zero_mem _
  | add u v _ _ hu hv => exact Submodule.add_mem _ hu hv
  | smul c u _ hu => exact Submodule.smul_mem _ c hu

/-- Pushing a low-degree function forward along a ring homomorphism. -/
