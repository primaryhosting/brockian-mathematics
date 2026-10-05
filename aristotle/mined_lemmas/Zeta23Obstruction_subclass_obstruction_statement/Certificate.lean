import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Obstruction

/-- An abstract *fixed-kernel pointwise-discard linear certificate*.

`ι` indexes the (finitely many) *species*.  The certificate is fixed once and for all:
it consists of a single kernel `R : ℝ → ℝ` (the analytic continuation of the certificate
kernel, in the concrete setting) together with strictly positive per-species charging
weights `w`.  The certificate charges a configuration linearly through `R`, and it
*discards* each term pointwise, so its validity requires each discarded term to be
nonnegative. -/
structure Certificate (ι : Type) where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- Per-species linear charging weights. -/
  w : ι → ℝ
  /-- The charging weights are strictly positive. -/
  hw : ∀ i, 0 < w i

variable {ι : Type}

/-- The linear charge assigned by the certificate to a configuration `z`, which records
the deep point attached to each species. -/

def Certificate.chargeWith [Fintype ι] (C : Certificate ι) (m : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, m i * (C.w i * C.R (z i))

/-- **Quantitative subclass obstruction.**

Once the fixed kernel has a single negative deep value `p`, the certificate's linear
charge is not merely negative but *unbounded below* along deep-pair configurations at
`p`: for every target `B` there is a nonnegative multiplicity vector whose charge on a
deep-pair configuration at `p` falls below `B`.  So no additive slack repairs the
pointwise-discard step. -/
