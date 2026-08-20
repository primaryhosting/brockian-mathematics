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
noncomputable def charge [Fintype ι] (C : Certificate ι) (z : Configuration ι) : ℝ :=
  ∑ i, C.w i * C.R (z i)

/-- The *termwise bound* required by the pointwise-discard step of the chain:
each individual contribution `R (z i)` must already be nonnegative, since the
argument discards the terms one at a time rather than exploiting cancellation. -/
def TermwiseBound (C : Certificate ι) (z : Configuration ι) : Prop :=
  ∀ i, 0 ≤ C.R (z i)

/-- A *deep-pair configuration*: two distinct species sit at the same deep
point. -/
def DeepPair (z : Configuration ι) : Prop :=
  ∃ i j, i ≠ j ∧ z i = z j

/-- The certificate is *valid* if its pointwise-discard termwise bound holds on
every configuration; equivalently (see `valid_iff_kernel_nonneg`) if the fixed
kernel is globally nonnegative. -/
def Valid (C : Certificate ι) : Prop :=
  ∀ z : Configuration ι, TermwiseBound C z

/-- Validity of a fixed-kernel pointwise-discard certificate is exactly global
nonnegativity of its kernel. -/
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
theorem subclass_obstruction_statement {ι : Type*} [Fintype ι]
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁)
    (C : Certificate ι) (z₀ : ℝ) (hz₀ : C.R z₀ < 0) :
    ∃ z : Configuration ι,
      DeepPair z ∧ z i₀ = z₀ ∧ z i₁ = z₀ ∧
      ¬ TermwiseBound C z ∧ charge C z < 0 ∧
      ¬ Valid C ∧ ¬ (∀ x : ℝ, 0 ≤ C.R x) := by
  refine ⟨fun _ => z₀, ⟨i₀, i₁, hne, rfl⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    exact absurd (h i₀) (not_le.mpr hz₀)
  · have hsum : charge C (fun _ => z₀) = (∑ i, C.w i) * C.R z₀ := by
      simp [charge, Finset.sum_mul]
    have hw : 0 < ∑ i, C.w i :=
      Finset.sum_pos (fun i _ => C.hw i) ⟨i₀, Finset.mem_univ i₀⟩
    rw [hsum]
    exact mul_neg_of_pos_of_neg hw hz₀
  · intro h
    exact absurd (h (fun _ => z₀) i₀) (not_le.mpr hz₀)
  · intro h
    exact absurd (h z₀) (not_le.mpr hz₀)

end Zeta23Obstruction

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

