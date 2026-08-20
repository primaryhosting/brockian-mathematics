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

theorem valid_iff_kernel_nonneg [Nonempty ι] (C : Certificate ι) :
    Valid C ↔ ∀ x : ℝ, 0 ≤ C.R x := by
  constructor
  · intro h x
    exact h (fun _ => x) (Classical.arbitrary ι)
  · intro h z i
    exact h (z i)

/-- **Abstract subclass obstruction.**

Given a fixed-kernel pointwise-discard linear certificate `C` over at least two
species, a single "bad deep value" `z₀` with `C.R z₀ < 0` (as produced by the
repaired witness) already destroys the certificate:

* there is a *deep-pair* configuration `z` (two distinct species `i₀ ≠ i₁`
  placed at the same deep point) on which
* the termwise bound of the pointwise-discard step **fails**, and
* the whole linear charge is strictly negative, so no rearrangement of the
  per-species charging can repair it; consequently
* the certificate is not valid, and its kernel is not globally nonnegative.

Thus: fixed kernel + pointwise discard + one bad deep value ⟹ invalid. -/
