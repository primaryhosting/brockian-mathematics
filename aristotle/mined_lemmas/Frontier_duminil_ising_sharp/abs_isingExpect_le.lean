/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

namespace Frontier

/-!
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

lemma abs_isingExpect_le (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (f : (V → Bool) → ℝ) (M : ℝ) (hf : ∀ σ, |f σ| ≤ M) :
    |isingExpect G β h f| ≤ M := by
  have hZ : 0 < isingPartition G β h := isingPartition_pos G β h
  rw [isingExpect, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
  calc |∑ σ : V → Bool, isingWeight G β h σ * f σ|
      ≤ ∑ σ : V → Bool, |isingWeight G β h σ * f σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : V → Bool, isingWeight G β h σ * M := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        rw [abs_mul, abs_of_pos (isingWeight_pos G β h σ)]
        exact mul_le_mul_of_nonneg_left (hf σ) (isingWeight_pos G β h σ).le
    _ = M * isingPartition G β h := by
        rw [isingPartition, ← Finset.sum_mul, mul_comm]

/-- Two-point functions of the Ising model are bounded by `1` in absolute value. -/
