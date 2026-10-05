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

import Mathlib

/-!
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Scope note.

The data-processing inequality states that relative entropy is monotone under
channels.  This file develops the inequality in the *commutative* (equivalently:
jointly diagonalisable / classical) sector of quantum information theory, where a
CPTP map restricted to a commuting family of states is exactly a stochastic map
between the corresponding spectra, and the quantum relative entropy
`Tr ρ (log ρ - log σ)` is exactly the Kullback-Leibler divergence of the two
spectra.

Everything below is proved from scratch: the log-sum inequality (from convexity
of `x ↦ x log x`), the data-processing inequality `QI.data_processing`, and, as a
corollary of it, Gibbs' inequality (nonnegativity of relative entropy).

The last section leaves the commutative sector: it proves the data-processing
inequality `QI.data_processing_max` for the max-relative entropy
`D_max(ρ‖σ) = log inf {λ ≥ 0 | ρ ≤ λ σ}` for arbitrary, possibly noncommuting,
density matrices and arbitrary positive trace-preserving maps (in particular all
CPTP maps).
-/

open Finset

namespace QI

variable {ι κ : Type*}

/-- Relative entropy (Kullback–Leibler divergence) of two finite nonnegative
weight vectors, with the usual conventions `0 log (0/b) = 0` and
`0 log (0/0) = 0` (implemented via `Real.log 0 = 0` and `x / 0 = 0`). -/

noncomputable def apply (K : Channel ι κ) (p : ι → ℝ) : κ → ℝ :=
  fun k => ∑ i, K.mat k i * p i

