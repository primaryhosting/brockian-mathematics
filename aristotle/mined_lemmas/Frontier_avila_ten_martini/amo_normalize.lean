import Mathlib
/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ENNReal

/-! ## The Hilbert space `ℓ²(ℤ, ℝ)` -/

/-- The Hilbert space `ℓ²(ℤ)` (real scalars) on which the almost Mathieu operator acts. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℝ) 2

/-! ## Multiplication and shift operators on `ℓ²(ℤ)` -/


theorem amo_normalize (lam alpha theta : ℝ) (hlam : lam ≠ 0) (hirr : Irrational alpha) :
    ∃ lam' alpha' theta' : ℝ, 0 < lam' ∧ Irrational alpha' ∧
      alpha' ∈ Set.Ioo (0 : ℝ) 1 ∧ theta' ∈ Set.Ico (0 : ℝ) 1 ∧
      amo lam alpha theta = amo lam' alpha' theta' := by
  -- the normalized flux
  set alpha' : ℝ := Int.fract alpha with halpha'
  have hirr' : Irrational alpha' := by
    rw [halpha', Int.fract]
    exact hirr.sub_intCast _
  have halphaIoo : alpha' ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne (Int.fract_nonneg alpha) ?_, Int.fract_lt_one alpha⟩
    intro h0
    exact hirr' (by rw [← h0]; exact ⟨0, by norm_num⟩)
  -- the base phase, adjusted so that the coupling becomes positive
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · refine ⟨-lam, alpha', Int.fract (theta + 1 / 2), by linarith, hirr', halphaIoo,
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have h1 : amo lam alpha theta = amo (-lam) alpha (theta + 1 / 2) :=
      (amo_neg_lam lam alpha theta).symm
    have h2 : amo (-lam) (alpha - (⌊alpha⌋ : ℤ)) (theta + 1 / 2 - (⌊theta + 1 / 2⌋ : ℤ))
        = amo (-lam) alpha (theta + 1 / 2) := amo_int_shift _ _ _ _ _
    rw [h1, ← h2]
    rfl
  · refine ⟨lam, alpha', Int.fract theta, hpos, hirr', halphaIoo,
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
    have h2 : amo lam (alpha - (⌊alpha⌋ : ℤ)) (theta - (⌊theta⌋ : ℤ)) = amo lam alpha theta :=
      amo_int_shift _ _ _ _ _
    rw [← h2]
    rfl

/-- **Ten Martini, Lean-checked reduction.**

The Ten Martini Problem — the spectrum of the almost Mathieu operator
`(H u) n = u (n+1) + u (n-1) + 2λ cos (2π (θ + n α)) u n` on `ℓ²(ℤ)` is a Cantor set for
every `λ ≠ 0` and every irrational `α` — is *equivalent* to the following, formally weaker
looking statement: for positive coupling `λ`, irrational flux `α ∈ (0,1)` and phase
`θ ∈ [0,1)`, the spectrum is nonempty, has empty interior, and has no isolated points.

The reduction uses: compactness of the spectrum of a bounded operator, the invariance of the
operator under integer shifts of `α` and `θ` and under `(λ, θ) ↦ (-λ, θ + 1/2)`, and the fact
that a subset of `ℝ` is totally disconnected exactly when it has empty interior. -/
