/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
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

/-!
## Mermin–Wagner: absence of continuous symmetry breaking in dimensions `d ≤ 2`

The mechanism behind the Mermin–Wagner theorem is an *energy–entropy* (spin-wave) estimate.
In a lattice system with a continuous internal symmetry, a configuration may be deformed by a
slowly varying, *finitely supported* rotation field `u : ℤ^d → ℝ`; to second order (which is
the relevant order, the first order term vanishing by the symmetry `θ ↦ -θ`) the free-energy
cost of the deformation at temperature `T` and coupling `J` is

  `(J / (2T)) * ∑_{⟨x,y⟩} (u x - u y)^2`,

i.e. `J / (2T)` times the *Dirichlet energy* of `u`.  Spontaneous breaking of the continuous
symmetry requires this cost to stay bounded away from zero when a fixed finite region is
rotated by a fixed angle `α` and the rotation is relaxed back to `0` at infinity; this
infimum is (up to the factor `J / (2T)`) the *capacity* of the region.

The theorem `Phys.mermin_wagner` below is exactly the statement that in dimension `d ≤ 2`
this cost vanishes: for every temperature `T > 0`, every coupling `J > 0`, every finite
region `A`, every rotation angle `α` and every `ε > 0`, there is a finitely supported
rotation field which rotates all of `A` by the full angle `α` at a free-energy cost less
than `ε`.  Equivalently: finite subsets of `ℤ^d` have zero capacity for `d ≤ 2` (`ℤ^d` is
recurrent/parabolic), so no continuous symmetry can be broken at any positive temperature.

The dimension enters through the divergence of the harmonic series: the shells
`{x : ‖x‖_∞ = s}` of `ℤ^d` with `d ≤ 2` contain `O(s)` points, so the harmonic profile
`u x = φ(‖x‖_∞)` used below has Dirichlet energy `O(1 / ∑_{s ≤ N} 1/s) → 0`.  In dimension
`d ≥ 3` shells contain `≍ s^{d-1}` points, the estimate fails, and indeed symmetry breaking
does occur.
-/

namespace Phys

variable {d : ℕ}

/-- The `i`-th unit vector of the lattice `ℤ^d`. -/

lemma sum_inv_sq_le (hd : d ≤ 2) (M : ℕ) :
    ∑ x ∈ (box M : Finset (Fin d → ℤ)),
        (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2) ≤ 12 * harm M := by
  classical
  have hmaps : ∀ x ∈ (box M : Finset (Fin d → ℤ)), normInf x ∈ Finset.range (M + 1) := by
    intro x hx
    have := mem_box.1 hx
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hinner : ∀ s ∈ Finset.range (M + 1),
      (∑ x ∈ (box M : Finset (Fin d → ℤ)) with normInf x = s,
        (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2))
        ≤ (if s = 0 then (0 : ℝ) else 12 / (s : ℝ)) := by
    intro s _
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [if_pos rfl]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [if_pos hx.2]
    · have hconst : (∑ x ∈ (box M : Finset (Fin d → ℤ)) with normInf x = s,
          (if normInf x = 0 then (0 : ℝ) else 1 / (normInf x : ℝ) ^ 2))
          = (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
              * (1 / (s : ℝ) ^ 2) := by
        rw [Finset.sum_congr rfl (fun x hx => ?_), Finset.sum_const, nsmul_eq_mul]
        simp only [Finset.mem_filter] at hx
        rw [hx.2, if_neg (by omega)]
      rw [hconst, if_neg (by omega)]
      have hcard : (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
          ≤ 12 * (s : ℝ) := by
        have hsub : ((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)) ⊆
            ((box s : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)) := by
          intro x hx
          simp only [Finset.mem_filter] at hx ⊢
          exact ⟨mem_box.2 (le_of_eq hx.2), hx.2⟩
        have h := (Finset.card_le_card hsub).trans (card_shell_le hd hs)
        exact_mod_cast h
      have hspos : (0 : ℝ) < s := by exact_mod_cast hs
      calc (((box M : Finset (Fin d → ℤ)).filter (fun x => normInf x = s)).card : ℝ)
            * (1 / (s : ℝ) ^ 2) ≤ (12 * (s : ℝ)) * (1 / (s : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 12 / (s : ℝ) := by field_simp
  refine (Finset.sum_le_sum hinner).trans ?_
  rw [Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range M,
      (if i + 1 = 0 then (0 : ℝ) else 12 / ((i + 1 : ℕ) : ℝ)) = 12 * (1 / ((i : ℝ) + 1)) := by
    intro i _
    rw [if_neg (by omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hz, ← Finset.mul_sum, if_pos rfl, add_zero]
  rfl

/-! ### Elementary properties of the Dirichlet energy -/

