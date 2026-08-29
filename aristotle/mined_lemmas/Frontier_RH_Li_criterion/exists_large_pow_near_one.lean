/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring below.)

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Li's criterion

Let `Z` be the multiset of (nontrivial) zeros of a completed zeta-type function.  Li's
coefficients are

`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`,

and Li's criterion states that all zeros lie on the critical line `Re ρ = 1/2` if and only if
`λ_n ≥ 0` for every `n ≥ 1`.

The content of the criterion is the Möbius change of variable `z = 1 - 1/ρ`, which maps the
critical line to the unit circle and the functional-equation symmetry `ρ ↦ 1 - ρ` to the
inversion `z ↦ 1/z`.  We prove the criterion for an arbitrary finite multiset of zeros which
avoids `0` and is stable under `ρ ↦ 1 - ρ`; this is the arithmetic-free core of Li's theorem
(the analytic input specific to `ζ`, namely the Hadamard product for the completed zeta
function, is what turns this statement into the statement about `ζ` itself).

The nontrivial direction uses a simultaneous recurrence statement on the unit circle
(`Frontier.exists_large_pow_near_one`): for finitely many unimodular numbers there are
arbitrarily large exponents `n` making all `n`-th powers simultaneously close to `1`.  This is
what forces a zero off the critical line to produce a negative Li coefficient.
-/

/-- The `n`-th Li coefficient attached to a finite multiset `Z` of zeros:
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/

lemma exists_large_pow_near_one {ι : Type} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) : ∃ n, N ≤ n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by
  set x : ℕ → (ι → ℂ) := fun m i => u i ^ m with hxdef
  have hx : ∀ m, x m ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro m
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    simp [hxdef, hu i]
  obtain ⟨a, -, ph, hph, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hx
  have hcauchy : CauchySeq (x ∘ ph) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨M, hM⟩ := hcauchy ε hε
  obtain ⟨p, hp1, hp2⟩ : ∃ p, M ≤ p ∧ N + ph M ≤ ph p :=
    ⟨max M (N + ph M), le_max_left _ _,
      le_trans (le_max_right M (N + ph M)) hph.le_apply⟩
  refine ⟨ph p - ph M, by omega, ?_⟩
  intro i
  have hnorm : ‖u i ^ (ph M)‖ = 1 := by simp [hu i]
  have hsplit : (u i ^ (ph p - ph M) - 1) * u i ^ (ph M) = u i ^ (ph p) - u i ^ (ph M) := by
    rw [sub_mul, one_mul, ← pow_add]
    congr 2
    omega
  have heq : ‖u i ^ (ph p - ph M) - 1‖ = ‖u i ^ (ph p) - u i ^ (ph M)‖ := by
    rw [← hsplit, norm_mul, hnorm, mul_one]
  have hd : dist (x (ph p) i) (x (ph M) i) ≤ dist (x (ph p)) (x (ph M)) := dist_le_pi_dist _ _ i
  have hlt := hM p hp1 M le_rfl
  simp only [Function.comp_apply] at hlt
  rw [heq]
  calc ‖u i ^ (ph p) - u i ^ (ph M)‖ = dist (x (ph p) i) (x (ph M) i) := by
        simp [hxdef, dist_eq_norm]
    _ ≤ dist (x (ph p)) (x (ph M)) := hd
    _ < ε := hlt

/-! ### Two computational lemmas -/

/-- Splitting off the modulus: `Re (z^n) = ‖z‖^n * Re ((z/‖z‖)^n)`. -/
