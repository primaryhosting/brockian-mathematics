/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- An abstract *fixed-kernel, pointwise-discard, linear* certificate.

`R` is the fixed kernel (the analytic object whose nonnegativity the certificate silently
assumes when it discards terms pointwise), and `weight` is the per-species linear charge. -/
structure Certificate (ι : Type*) where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- The per-species linear charge weights. -/
  weight : ι → ℝ
  /-- The charging is nonnegative (weights are a charge, not a signed measure). -/
  weight_nonneg : ∀ i : ι, 0 ≤ weight i

/-- Configuration data: each species is placed at a *deep point* of the kernel. -/
structure Configuration (ι : Type*) where
  /-- The deep point at which a given species sits. -/
  deepPoint : ι → ℝ

variable {ι : Type*}

/-- The linear functional the certificate evaluates on configuration data. -/
noncomputable def charge [Fintype ι] (C : Certificate ι) (cfg : Configuration ι) : ℝ :=
  ∑ i : ι, C.weight i * C.R (cfg.deepPoint i)

/-- The *termwise bound* on which the pointwise-discard step of the chain rests: every
individual charged term is nonnegative, so that discarding it can only decrease the total. -/
def TermwiseBound (C : Certificate ι) (cfg : Configuration ι) : Prop :=
  ∀ i : ι, 0 ≤ C.weight i * C.R (cfg.deepPoint i)

/-- A *deep-pair configuration at `z`*: at least two distinct species are pinned at the same
deep point `z` (the abstract shadow of a conjugate pair of deep zeros). -/
def IsDeepPairAt (cfg : Configuration ι) (z : ℝ) : Prop :=
  ∃ i j : ι, i ≠ j ∧ cfg.deepPoint i = z ∧ cfg.deepPoint j = z

/-- The certificate is *valid against deep-pair configurations* when its pointwise-discard
step is legitimate on every such configuration. -/
def ValidOnDeepPairs (C : Certificate ι) : Prop :=
  ∀ (z : ℝ) (cfg : Configuration ι), IsDeepPairAt cfg z → TermwiseBound C cfg

/-- The constant configuration placing every species at the point `z`. -/
def constConfig (z : ℝ) : Configuration ι := ⟨fun _ => z⟩

theorem isDeepPairAt_constConfig [Nontrivial ι] (z : ℝ) :
    IsDeepPairAt (constConfig (ι := ι) z) z := by
  obtain ⟨i, j, hij⟩ := (inferInstance : Nontrivial ι)
  exact ⟨i, j, hij, rfl, rfl⟩

/-- **Abstract subclass obstruction.**

For a fixed-kernel pointwise-discard linear certificate with strictly positive per-species
charging, a single deep value at which the kernel is negative (the repaired witness `z`,
`C.R z < 0`) already produces a deep-pair configuration on which the chain's termwise bound
fails and on which the linear charge is itself negative; consequently the certificate is not
valid against deep-pair configurations. -/
theorem subclass_obstruction_statement {ι : Type*} [Fintype ι] [Nontrivial ι]
    (C : Certificate ι) (hw : ∀ i : ι, 0 < C.weight i)
    (z : ℝ) (hz : C.R z < 0) :
    (∃ cfg : Configuration ι,
        IsDeepPairAt cfg z ∧ ¬ TermwiseBound C cfg ∧ charge C cfg < 0) ∧
      ¬ ValidOnDeepPairs C := by
  have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  obtain ⟨i₀, -⟩ := hne
  have hterm : ∀ i : ι, C.weight i * C.R z < 0 := fun i =>
    mul_neg_of_pos_of_neg (hw i) hz
  have hfail : ¬ TermwiseBound C (constConfig (ι := ι) z) := by
    intro h
    exact absurd (h i₀) (not_le.mpr (hterm i₀))
  have hcharge : charge C (constConfig (ι := ι) z) < 0 := by
    have : ∑ i : ι, C.weight i * C.R z < ∑ _i : ι, (0 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hterm i
    simpa [charge, constConfig] using this
  refine ⟨⟨constConfig z, isDeepPairAt_constConfig z, hfail, hcharge⟩, ?_⟩
  intro hvalid
  exact hfail (hvalid z _ (isDeepPairAt_constConfig z))

/-- Sanity check: the hypotheses of `subclass_obstruction_statement` are satisfiable, so the
obstruction is not vacuous. -/
example :
    (∃ cfg : Configuration (Fin 2),
        IsDeepPairAt cfg (-1) ∧
          ¬ TermwiseBound ⟨fun x => x, fun _ => 1, by norm_num⟩ cfg ∧
          charge ⟨fun x => x, fun _ => 1, by norm_num⟩ cfg < 0) ∧
      ¬ ValidOnDeepPairs (⟨fun x => x, fun _ => 1, by norm_num⟩ : Certificate (Fin 2)) :=
  subclass_obstruction_statement ⟨fun x => x, fun _ => 1, by norm_num⟩ (by norm_num) (-1)
    (by norm_num)

end Zeta23Obstruction

