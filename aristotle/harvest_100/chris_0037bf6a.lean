/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

namespace Phys

/-- The (Gibbs–Shannon / von Neumann) entropy of a system whose microstates are indexed by `ι`
and occupied with probabilities `p`, measured in units of the Boltzmann constant `k`:
`S = -k ∑ᵢ pᵢ log pᵢ`. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (k : ℝ) (p : ι → ℝ) : ℝ :=
  k * ∑ i, -(p i * Real.log (p i))

/-- The mean energy `E = ∑ᵢ pᵢ Eᵢ` of a system with microstate energies `Eℓ` occupied with
probabilities `p`. -/
noncomputable def meanEnergy {ι : Type*} [Fintype ι] (p Eℓ : ι → ℝ) : ℝ := ∑ i, p i * Eℓ i

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of radius `R`
and energy `E`. -/
noncomputable def bekensteinBound (k hbar c R E : ℝ) : ℝ := 2 * Real.pi * k * R * E / (hbar * c)

/-- Gibbs' inequality in the form needed below: if `p` is a probability vector and
`q i = exp (-(β * Eℓ i))` sums to one, then `-∑ pᵢ log pᵢ ≤ β ∑ pᵢ Eᵢ`. -/
theorem gibbs_entropy_le {ι : Type*} [Fintype ι] (beta : ℝ) (Eℓ p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq : ∑ i, Real.exp (-(beta * Eℓ i)) = 1) :
    ∑ i, -(p i * Real.log (p i)) ≤ beta * ∑ i, p i * Eℓ i := by
  -- Termwise: `-pᵢ log pᵢ - β pᵢ Eᵢ ≤ qᵢ - pᵢ`, and the right side sums to `0`.
  have key : ∀ i : ι, -(p i * Real.log (p i)) - beta * (p i * Eℓ i)
      ≤ Real.exp (-(beta * Eℓ i)) - p i := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with h0 | hpos
    · simp [← h0, Real.exp_pos (-(beta * Eℓ i)) |>.le]
    · have hlog : Real.log (Real.exp (-(beta * Eℓ i)) / p i)
          ≤ Real.exp (-(beta * Eℓ i)) / p i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hexp : Real.log (Real.exp (-(beta * Eℓ i)) / p i)
          = -(beta * Eℓ i) - Real.log (p i) := by
        rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hpos), Real.log_exp]
      rw [hexp] at hlog
      have := mul_le_mul_of_nonneg_left hlog hpos.le
      have hdiv : p i * (Real.exp (-(beta * Eℓ i)) / p i - 1)
          = Real.exp (-(beta * Eℓ i)) - p i := by
        field_simp
      rw [hdiv] at this
      nlinarith [this]
  have hsum : ∑ i, (-(p i * Real.log (p i)) - beta * (p i * Eℓ i))
      ≤ ∑ i, (Real.exp (-(beta * Eℓ i)) - p i) := Finset.sum_le_sum fun i _ => key i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq, hp1, ← Finset.mul_sum] at hsum
  linarith

/-- **The Bekenstein bound.**

For a system confined to a region of radius `R`, with microstates indexed by `ι`, microstate
energies `Eℓ` and occupation probabilities `p`, the entropy satisfies

`S ≤ 2 π k R E / (ℏ c)`,

where `E` is the mean energy of the system.  The hypothesis `hvac` is the statement that the
reference (vacuum / modular) state at the Unruh inverse temperature `β = 2 π R / (ℏ c)` associated
with the region is a normalized state, i.e. has vanishing free energy; the bound is then exactly
the nonnegativity of the relative entropy of the system's state with respect to it.

(The positivity hypothesis `hR : 0 < R` records that `R` is a radius; it is not needed by the
proof, which only uses the normalization `hvac`.) -/
theorem bekenstein_bound {ι : Type*} [Fintype ι]
    (k hbar c R : ℝ) (hk : 0 < k) (hhbar : 0 < hbar) (hc : 0 < c) (hR : 0 < R)
    (Eℓ p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hvac : ∑ i, Real.exp (-((2 * Real.pi * R / (hbar * c)) * Eℓ i)) = 1) :
    entropy k p ≤ bekensteinBound k hbar c R (meanEnergy p Eℓ) := by
  have h := gibbs_entropy_le (2 * Real.pi * R / (hbar * c)) Eℓ p hp0 hp1 hvac
  have hkc : entropy k p ≤ k * ((2 * Real.pi * R / (hbar * c)) * ∑ i, p i * Eℓ i) := by
    unfold entropy
    exact mul_le_mul_of_nonneg_left h hk.le
  have hne : hbar * c ≠ 0 := by positivity
  unfold bekensteinBound meanEnergy
  calc entropy k p ≤ k * ((2 * Real.pi * R / (hbar * c)) * ∑ i, p i * Eℓ i) := hkc
    _ = 2 * Real.pi * k * R * (∑ i, p i * Eℓ i) / (hbar * c) := by field_simp

/-- The Bekenstein bound is sharp: a two-level system whose levels both sit at the energy
`E = (ℏ c log 2) / (2 π R)`, equally occupied, satisfies the hypotheses of `bekenstein_bound`
and saturates it.  In particular the hypotheses are not vacuous. -/
theorem bekenstein_bound_sharp
    (k hbar c R : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) (hR : 0 < R) :
    ∃ (Eℓ p : Fin 2 → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      (∑ i, Real.exp (-((2 * Real.pi * R / (hbar * c)) * Eℓ i)) = 1) ∧
      entropy k p = bekensteinBound k hbar c R (meanEnergy p Eℓ) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hbc : hbar * c ≠ 0 := by positivity
  have hden : 2 * Real.pi * R ≠ 0 := by positivity
  refine ⟨fun _ => hbar * c * Real.log 2 / (2 * Real.pi * R), fun _ => 1 / 2,
    fun _ => by norm_num, by simp, ?_, ?_⟩
  · have h1 : (2 * Real.pi * R / (hbar * c)) * (hbar * c * Real.log 2 / (2 * Real.pi * R))
        = Real.log 2 := by field_simp
    simp [h1, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  · unfold entropy bekensteinBound meanEnergy
    simp only [Fin.sum_univ_two, one_div, Real.log_inv]
    field_simp

#print axioms Phys.bekenstein_bound
#print axioms Phys.bekenstein_bound_sharp

end Phys

