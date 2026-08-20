import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma map_mem_Deg {K : Type*} [CommRing K] (φ : F →+* K) {f : Cube n → F} {D : ℕ}
    (hf : f ∈ Deg F n D) : (fun x => φ (f x)) ∈ Deg K n D := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      have : (fun x => φ (mono F S x)) = mono K S := by
        funext x
        simp only [mono, coord, map_prod]
        exact Finset.prod_congr rfl (fun i _ => by by_cases h : x i <;> simp [h])
      rw [this]
      exact mono_mem_Deg hS
  | zero =>
      have h0 : (fun x : Cube n => φ ((0 : Cube n → F) x)) = 0 := by funext x; simp
      rw [h0]; exact Submodule.zero_mem _
  | add u v _ _ hu hv =>
      have : (fun x => φ ((u + v) x)) = (fun x => φ (u x)) + (fun x => φ (v x)) := by
        funext x; simp
      rw [this]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu =>
      have : (fun x => φ ((c • u) x)) = φ c • (fun x => φ (u x)) := by
        funext x; simp
      rw [this]; exact Submodule.smul_mem _ _ hu

/-- Indicator function of a point of the cube. -/
