import Mathlib

/-!
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-!
## An abstract finite-dimensional model of a fixed-kernel pointwise-discard certificate

We model the "certificate chain" abstractly.  There are finitely many *species*
(indexed by `Fin n`), each carrying a nonnegative *weight*.  A *configuration*
assigns to each species a *deep point* of the real line.  The certificate is
built from one *fixed kernel* `R : ℝ → ℝ`: the charge attached to a
configuration is the linear functional

`charge C z = ∑ i, weight i * R (z i)`,

and the *pointwise-discard* step of the chain is only legitimate when each
individual term is discarded upwards, i.e. when the termwise bound
`0 ≤ weight i * R (z i)` holds for every species and every configuration.
The content of the obstruction is purely about this quantifier structure: the
kernel is fixed *before* the configuration is chosen, so a single point `z₀`
with `R z₀ < 0` can be fed simultaneously to a pair of species, breaking the
termwise bound and even making the whole linear charge negative.
-/

/-- A *fixed-kernel pointwise-discard linear certificate* over `n` species:
a kernel `R : ℝ → ℝ`, chosen once and for all, together with nonnegative
per-species charging weights. -/
structure Certificate (n : ℕ) where
  /-- The fixed kernel used at every deep point. -/
  R : ℝ → ℝ
  /-- The per-species linear charging weights. -/
  weight : Fin n → ℝ
  /-- The weights are nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i

/-- A *configuration*: an assignment of a deep point to each species. -/
abbrev Config (n : ℕ) : Type := Fin n → ℝ

variable {n : ℕ}

/-- The linear charge attached by a certificate to a configuration. -/
noncomputable def charge (C : Certificate n) (z : Config n) : ℝ :=
  ∑ i, C.weight i * C.R (z i)

/-- The termwise bound underlying the pointwise-discard step: every individual
species contribution must be nonnegative. -/
def TermwiseBound (C : Certificate n) (z : Config n) : Prop :=
  ∀ i, 0 ≤ C.weight i * C.R (z i)

/-- A certificate is *valid* when its pointwise-discard step is legitimate on
every configuration. -/
def Valid (C : Certificate n) : Prop :=
  ∀ z : Config n, TermwiseBound C z

/-- `z` is a *deep-pair configuration at `z₀` for the species `i ≠ j`*: the two
distinct species `i` and `j` are both placed at the deep point `z₀`. -/
def DeepPair (i j : Fin n) (z₀ : ℝ) (z : Config n) : Prop :=
  i ≠ j ∧ z i = z₀ ∧ z j = z₀

/-- The kernel positivity hypothesis `h_pos` that the certificate needs. -/
def KernelNonneg (C : Certificate n) : Prop :=
  ∀ x : ℝ, 0 ≤ C.R x

/-- On a constant configuration the charge factors as total weight times the
kernel value. -/
theorem charge_const (C : Certificate n) (z₀ : ℝ) :
    charge C (fun _ => z₀) = (∑ i, C.weight i) * C.R z₀ := by
  simp [charge, Finset.sum_mul]

/-- A valid certificate (in the above pointwise-discard sense) forces the
kernel to be nonnegative wherever some species has positive weight. -/
theorem kernelNonneg_of_valid (C : Certificate n) (i : Fin n)
    (hw : 0 < C.weight i) (hV : Valid C) : KernelNonneg C := by
  intro x
  have h := hV (fun _ => x) i
  exact nonneg_of_mul_nonneg_right h hw

/-!
## The subclass obstruction

Fixed kernel + pointwise discard + one bad deep value ⟹ the certificate is
invalid, and it already fails on an explicit deep-pair configuration.
-/

/-- **Abstract subclass obstruction.**  Let `C` be a fixed-kernel
pointwise-discard linear certificate over finitely many species, and let
`i ≠ j` be two species carrying strictly positive charging weights.  If the
(analytically continued) kernel takes a negative value at some deep point `z₀`
— the repaired witness — then there is a *deep-pair configuration* at `z₀` for
`i` and `j` on which

* the termwise (pointwise-discard) bound fails at both species of the pair,
* hence the termwise bound fails outright,
* and the total linear charge of the certificate is strictly negative;

consequently the certificate is invalid and its kernel-positivity hypothesis
`h_pos` cannot hold. -/
theorem subclass_obstruction_statement
    (C : Certificate n) (i j : Fin n) (hij : i ≠ j)
    (hwi : 0 < C.weight i) (hwj : 0 < C.weight j)
    (z₀ : ℝ) (hz₀ : C.R z₀ < 0) :
    ∃ z : Config n,
      DeepPair i j z₀ z ∧
      C.weight i * C.R (z i) < 0 ∧
      C.weight j * C.R (z j) < 0 ∧
      C.weight i * C.R (z i) + C.weight j * C.R (z j) < 0 ∧
      ¬ TermwiseBound C z ∧
      charge C z < 0 ∧
      ¬ Valid C ∧
      ¬ KernelNonneg C := by
  refine ⟨fun _ => z₀, ⟨hij, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_pos_of_neg hwi hz₀
  · exact mul_neg_of_pos_of_neg hwj hz₀
  · exact add_neg (mul_neg_of_pos_of_neg hwi hz₀) (mul_neg_of_pos_of_neg hwj hz₀)
  · intro hT
    exact absurd (hT i) (not_le.mpr (mul_neg_of_pos_of_neg hwi hz₀))
  · -- the whole linear charge is negative: total weight is positive
    have hsum : 0 < ∑ k, C.weight k := by
      have hle : C.weight i + C.weight j ≤ ∑ k, C.weight k := by
        have : ∑ k ∈ ({i, j} : Finset (Fin n)), C.weight k ≤ ∑ k, C.weight k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => C.weight_nonneg k)
        rwa [Finset.sum_pair hij] at this
      linarith
    rw [charge_const]
    exact mul_neg_of_pos_of_neg hsum hz₀
  · intro hV
    exact absurd (hV (fun _ => z₀) i) (not_le.mpr (mul_neg_of_pos_of_neg hwi hz₀))
  · intro hR
    exact absurd (hR z₀) (not_le.mpr hz₀)

end Zeta23Obstruction

