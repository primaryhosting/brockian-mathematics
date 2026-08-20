import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Obstruction

/-- A *fixed-kernel pointwise-discard linear certificate* over a finite set of
"species" `ι`.

* `R` is the fixed kernel: a single function of one real variable, chosen once
  and for all, independent of the configuration it is later evaluated on
  (this is the "fixed kernel" part).
* `w i` is the positive charging weight attached to species `i`
  (the "per-species linear charging" part). -/
structure Certificate (ι : Type*) where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- The per-species charging weights. -/
  w : ι → ℝ
  /-- The weights are strictly positive. -/
  hw : ∀ i, 0 < w i

variable {ι : Type*}

/-- A *configuration*: each species `i` is placed at a deep point `z i ∈ ℝ`. -/
abbrev Configuration (ι : Type*) := ι → ℝ

/-- The linear charge functional of the certificate evaluated on a
configuration: a linear form in the vector `(R (z i))ᵢ` with the fixed
positive weights as coefficients. -/

def Valid (C : Certificate ι) : Prop :=
  ∀ z : Configuration ι, TermwiseBound C z

/-- Validity of a fixed-kernel pointwise-discard certificate is exactly global
nonnegativity of its kernel. -/
