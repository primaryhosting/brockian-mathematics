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
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

We work with finite-dimensional quantum systems, i.e. complex matrices `Matrix n n ℂ`.

* `QI.Channel ι n m` is a CPTP map (quantum channel) given in Kraus form: a family of Kraus
  operators `K i : Matrix m n ℂ` with `∑ i, (K i)ᴴ * K i = 1`.  `QI.Channel.map` is the
  Schrödinger picture action `X ↦ ∑ i, K i * X * (K i)ᴴ`; it is proved to be positive
  (`QI.Channel.map_posSemidef`) and trace preserving (`QI.Channel.trace_map`).
* `QI.posPartTrace X` is the trace of the positive part of a Hermitian matrix, defined
  variationally as `sup { Re Tr (X P) : 0 ≤ P ≤ 1 }` and valued in `ℝ≥0∞`.  Theorem
  `QI.posPartTrace_eq_sum_eigenvalues` identifies it with `∑ᵢ (λᵢ)₊`, the usual
  `Tr X₊`, for Hermitian `X`.
* `QI.posPartTrace_map_le` is the data processing inequality for the hockey-stick
  divergence: `Tr (Φ(X))₊ ≤ Tr X₊` for every channel `Φ`.
* `QI.relEntropy ρ σ` is the quantum relative entropy, expressed through Frenkel's integral
  formula
  `D(ρ ‖ σ) = ∫_0^∞ (Tr (ρ - tσ)₊ - (Tr ρ) (1 - t)₊) dt / t`,
  written as a lower Lebesgue integral (so its value lies in `ℝ≥0∞`, with `∞` allowed).
* `QI.data_processing` is the **data processing inequality**: `D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`
  for every channel `Φ` and all `ρ`, `σ`.

## Remarks on the definition of relative entropy

That the integral formula above computes `Tr ρ (log ρ - log σ)` for arbitrary (in particular
non-commuting) density matrices is a theorem of P. E. Frenkel, *Integral formula for quantum
relative entropy implies data processing inequality*, J. Phys. A **56** (2023) 385303;
that identification is *not* formalised here.  What is formalised, besides the data processing
inequality itself, are the following consistency results:

* `QI.relEntropy_diagonal` (in `RequestProject.ClassicalCase`): for commuting states, i.e. for
  diagonal density matrices with entries given by probability vectors `p`, `q` with `q > 0`,
  the formula returns the classical Kullback-Leibler divergence `∑ᵢ pᵢ log (pᵢ / qᵢ)`.
* `QI.relEntropy_self`: `D(ρ ‖ ρ) = 0`.
* `QI.relEntropy_conj_unitary`: invariance under simultaneous unitary conjugation.

The data processing inequality proved here is in fact slightly stronger than the standard
statement in two ways: the integrand inequality only uses that the dual of the channel maps
effects to effects, and the states `ρ`, `σ` are arbitrary matrices.
-/

open scoped ENNReal ComplexOrder
open Matrix MeasureTheory

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- An *effect* (or *test operator*) is a matrix `P` with `0 ≤ P ≤ 1`. -/

theorem relEntropy_diagonal (p q : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    relEntropy (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
      = ENNReal.ofReal (∑ i, p i * Real.log (p i / q i)) := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      (posPartTrace ((Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
            - (t : ℂ) • (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)))
          - ENNReal.ofReal ((Matrix.diagonal fun i => ((p i : ℝ) : ℂ)).trace.re
              * max 0 (1 - t))) / ENNReal.ofReal t
        = ENNReal.ofReal (∑ i, fren (p i) (q i) t) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [diagonal_sub_smul, posPartTrace_diagonal, re_trace_diagonal, hp1, one_mul,
      max_comm (0 : ℝ) (1 - t), ← ENNReal.ofReal_sub _ (le_max_right _ _),
      ← ENNReal.ofReal_div_of_pos ht0]
    congr 1
    rw [sum_fren p q hp t, hp1, one_mul]
  have hint : ∀ i : n, IntegrableOn (fren (p i) (q i)) (Ioi 0) :=
    fun i => integrableOn_fren (p i) (q i) (hp i) (hq i)
  have hintsum : IntegrableOn (fun t => ∑ i, fren (p i) (q i) t) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => hint i
  rw [relEntropy, setLIntegral_congr_fun measurableSet_Ioi hcongr,
    ← ofReal_integral_eq_lintegral_ofReal hintsum
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
        fun t ht => sum_fren_nonneg p q hp hp1 hq1 ht))]
  congr 1
  rw [integral_finset_sum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ => integral_fren (p i) (q i) (hp i) (hq i)

end QI

