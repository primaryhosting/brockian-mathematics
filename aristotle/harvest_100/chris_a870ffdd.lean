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
def Certificate.charge [Fintype ι] (C : Certificate ι) (z : ι → ℝ) : ℝ :=
  ∑ i, C.w i * C.R (z i)

/-- The *termwise bound* required by the pointwise-discard step: every term of the
linear charge must be discardable, i.e. the kernel must be nonnegative at each deep
point of the configuration. -/
def Certificate.TermwiseBound (C : Certificate ι) (z : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ C.R (z i)

/-- The certificate is *valid* against a configuration when the pointwise-discard step
goes through, i.e. when the termwise bound holds. -/
def Certificate.ValidAgainst (C : Certificate ι) (z : ι → ℝ) : Prop :=
  C.TermwiseBound z

/-- A configuration `z` is a *deep-pair configuration at `p`* when at least two distinct
species sit at the deep point `p`. -/
def IsDeepPair (z : ι → ℝ) (p : ℝ) : Prop :=
  ∃ i j : ι, i ≠ j ∧ z i = p ∧ z j = p

/-- **Subclass obstruction (abstract form).**

A fixed-kernel pointwise-discard linear certificate with a negative deep value is
invalid against deep-pair configurations.

Precisely: for a certificate `C` on at least two species, if the fixed kernel `C.R`
takes a negative value at some point `p` (the repaired witness), then there is a
deep-pair configuration at `p` against which the certificate is *not* valid — the
termwise bound of the pointwise-discard step fails — and on which the total linear
charge is itself negative.

The content is the quantifier structure: the kernel is fixed *before* the configuration
is chosen, so a single bad deep value suffices to defeat the whole chain. -/
theorem subclass_obstruction_statement [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (C : Certificate ι) (p : ℝ) (hp : C.R p < 0) :
    ∃ z : ι → ℝ, IsDeepPair z p ∧ ¬ C.ValidAgainst z ∧ C.charge z < 0 := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hι
  refine ⟨fun _ => p, ⟨i, j, hij, rfl, rfl⟩, ?_, ?_⟩
  · intro h
    exact absurd (h i) (not_le.mpr hp)
  · have hsum : (0 : ℝ) < ∑ k, C.w k := by
      refine Finset.sum_pos (fun k _ => C.hw k) ?_
      exact ⟨i, Finset.mem_univ i⟩
    have : C.charge (fun _ => p) = (∑ k, C.w k) * C.R p := by
      simp [Certificate.charge, Finset.sum_mul]
    rw [this]
    exact mul_neg_of_pos_of_neg hsum hp

/-- The linear charge of a configuration carrying per-species *multiplicities* `m`
(nonnegative occupation numbers), charged linearly through the fixed kernel. -/
def Certificate.chargeWith [Fintype ι] (C : Certificate ι) (m : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, m i * (C.w i * C.R (z i))

/-- **Quantitative subclass obstruction.**

Once the fixed kernel has a single negative deep value `p`, the certificate's linear
charge is not merely negative but *unbounded below* along deep-pair configurations at
`p`: for every target `B` there is a nonnegative multiplicity vector whose charge on a
deep-pair configuration at `p` falls below `B`.  So no additive slack repairs the
pointwise-discard step. -/
theorem charge_unbounded_below_of_neg_deep_value [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (C : Certificate ι) (p : ℝ) (hp : C.R p < 0) (B : ℝ) :
    ∃ (m : ι → ℝ) (z : ι → ℝ), (∀ i, 0 ≤ m i) ∧ IsDeepPair z p ∧
      ¬ C.ValidAgainst z ∧ C.chargeWith m z < B := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hι
  have hsum : (0 : ℝ) < ∑ k, C.w k := Finset.sum_pos (fun k _ => C.hw k) ⟨i, Finset.mem_univ i⟩
  have hden : (0 : ℝ) < (∑ k, C.w k) * (-C.R p) := mul_pos hsum (neg_pos.mpr hp)
  obtain ⟨t, ht⟩ := exists_gt (max 0 ((-B + 1) / ((∑ k, C.w k) * (-C.R p))))
  have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht)
  refine ⟨fun _ => t, fun _ => p, fun _ => ht0, ⟨i, j, hij, rfl, rfl⟩, ?_, ?_⟩
  · intro h
    exact absurd (h i) (not_le.mpr hp)
  · have hval : C.chargeWith (fun _ => t) (fun _ => p) = t * ((∑ k, C.w k) * C.R p) := by
      simp [Certificate.chargeWith, Finset.mul_sum, Finset.sum_mul]
    rw [hval]
    have hlt : (-B + 1) / ((∑ k, C.w k) * (-C.R p)) < t :=
      lt_of_le_of_lt (le_max_right _ _) ht
    have hkey : -B + 1 < t * ((∑ k, C.w k) * (-C.R p)) := by
      rw [div_lt_iff₀ hden] at hlt
      linarith
    nlinarith [hkey]

/-- Contrapositive packaging: if the certificate survives the pointwise-discard step
against *every* configuration, then its fixed kernel is globally nonnegative. -/
theorem kernel_nonneg_of_valid [Fintype ι] (hι : 2 ≤ Fintype.card ι) (C : Certificate ι)
    (hvalid : ∀ z : ι → ℝ, C.ValidAgainst z) : ∀ x, 0 ≤ C.R x := by
  intro x
  by_contra hx
  obtain ⟨z, -, hbad, -⟩ := subclass_obstruction_statement hι C x (not_le.mp hx)
  exact hbad (hvalid z)

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

