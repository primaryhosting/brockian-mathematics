import Mathlib

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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file constructs an explicit sequence in `[0, 1)` whose empirical distribution is
asymptotically the uniform one: for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
the first `N` terms lying in `[a, b)` converges to `b - a`.

The construction is the "triangular block" sequence
`0/1 ; 0/2, 1/2 ; 0/3, 1/3, 2/3 ; 0/4, …` .
-/

open Filter Topology

namespace Brockian.Equidistribution

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/

lemma seq_isEquidistributed : IsEquidistributed seq := by
  intro a b ha hab hb
  have key : ∀ N : ℕ, 1 ≤ N →
      |((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)| ≤ errBound N := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    obtain ⟨K, h1, h2, h3⟩ := exists_block_index N
    have hbd := cnt_bound a b ha hab hb N K h1 h2
    have hnum : |((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)| ≤ 3 * Real.sqrt (2 * N) + 3 := by
      refine hbd.trans ?_
      linarith
    have heq : ((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)
        = (((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)) / (N : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    unfold errBound
    gcongr
  have hz : Tendsto (fun N : ℕ => ((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ errBound_tendsto
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa [Real.norm_eq_abs] using key N hN
  have hfin := hz.add_const (b - a)
  simpa [cnt] using hfin

/-- **Main theorem.** There exists an equidistributed sequence in `[0, 1)`: the asymptotic
uniform distribution of empirical counts is realised by an explicit sequence, with no
hypotheses assumed. -/
