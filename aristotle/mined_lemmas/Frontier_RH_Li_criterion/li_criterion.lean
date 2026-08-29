/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Complex Filter

/-! ## Li coefficients of a finite family of zeros -/

/-- The `n`-th **Li coefficient** attached to a finite multiset `Z` of (candidate) zeros:
`λ_n(Z) = ∑_{ρ ∈ Z} Re (1 - (1 - 1/ρ)^n)`.  This is the standard Bombieri–Lagarias
expression of Li's coefficients as a sum over the zeros. -/

theorem li_criterion {Z : Multiset ℂ} (h0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hsym : Z.map (fun ρ : ℂ => 1 - ρ) = Z) :
    (∀ ρ ∈ Z, ρ.re = 1 / 2) ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ liCoeff Z n := by
  have hmem : ∀ ρ ∈ Z, 1 - ρ ∈ Z := by
    intro ρ hρ
    have : (1 - ρ) ∈ Z.map (fun ρ : ℂ => 1 - ρ) := Multiset.mem_map_of_mem _ hρ
    rwa [hsym] at this
  have h1 : ∀ ρ ∈ Z, ρ ≠ 1 := by
    intro ρ hρ hcon
    have : (1 : ℂ) - ρ ∈ Z := hmem ρ hρ
    rw [hcon, sub_self] at this
    exact h0 0 this rfl
  constructor
  · intro h n _
    refine liCoeff_nonneg_of_norm_eq_one ?_ n
    intro ρ hρ
    exact (re_eq_half_iff_norm_eq_one (h0 ρ hρ)).1 (h ρ hρ)
  · intro h ρ hρ
    rw [re_eq_half_iff_norm_eq_one (h0 ρ hρ)]
    -- The Möbius image cannot have modulus `> 1` …
    have hno : ∀ σ ∈ Z, ¬ (1 < ‖1 - 1 / σ‖) := by
      intro σ hσ hgt
      obtain ⟨n, hn1, hneg⟩ := exists_liCoeff_neg h0 h1 hσ hgt
      exact absurd (h n hn1) (not_le.2 hneg)
    -- … and by the symmetry `ρ ↦ 1 - ρ` it cannot have modulus `< 1` either.
    have hprod := moebius_one_sub (h0 ρ hρ) (h1 ρ hρ)
    have hnorms : ‖1 - 1 / (1 - ρ)‖ * ‖1 - 1 / ρ‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    have hle₁ : ‖1 - 1 / ρ‖ ≤ 1 := not_lt.1 (hno ρ hρ)
    have hle₂ : ‖1 - 1 / (1 - ρ)‖ ≤ 1 := not_lt.1 (hno _ (hmem ρ hρ))
    have hpos : 0 < ‖1 - 1 / ρ‖ := by
      have := moebius_ne_zero (h0 ρ hρ) (h1 ρ hρ)
      positivity
    nlinarith [hnorms, hle₁, hle₂, hpos]

/-! ## Nontrivial zeros of `ζ` -/

/-- `ζ` does not vanish at the negative odd integers. -/
