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

theorem nontrivialZeros_ne_neg_nat {s : ℂ} (hs : s ∈ nontrivialZeros) (n : ℕ) : s ≠ -(n : ℂ) := by
  obtain ⟨hz, htriv, -⟩ := hs
  intro hcon
  subst hcon
  rcases Nat.even_or_odd n with he | ho
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [Nat.cast_zero, neg_zero, riemannZeta_zero] at hz
      norm_num at hz
    · obtain ⟨j, hj⟩ := he
      have hjpos : 1 ≤ j := by omega
      obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact htriv ⟨i, by rw [hj, hi]; push_cast; ring⟩
  · obtain ⟨i, hi⟩ := ho
    apply zeta_neg_odd_ne_zero i
    rw [← hz, hi]
    push_cast
    ring_nf

/-- Nontrivial zeros are nonzero. -/
