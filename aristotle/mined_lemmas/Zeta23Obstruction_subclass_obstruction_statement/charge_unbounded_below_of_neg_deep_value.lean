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
