/-
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polya Isomer Count
Category: Chemistry
Target: Chem.polya_isomer_count
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

namespace Chem

open MulAction

attribute [local instance] arrowAction

section

variable {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [Fintype P] [MulAction G P]
variable {C : Type*} [Fintype C]

/-- Burnside's lemma, phrased with `Nat.card`. -/

lemma fixed_apply_zpow {g : G} {f : P → C} (hf : f ∈ fixedBy (P → C) g) (n : ℤ) (p : P) :
    f ((g ^ n) • p) = f p := by
  have h1 : ∀ q : P, f (g⁻¹ • q) = f q := fun q => congrFun hf q
  have hg : ∀ q : P, f (g • q) = f q := by
    intro q
    have h2 := h1 (g • q)
    rw [inv_smul_smul] at h2
    exact h2.symm
  have hginv : ∀ q : P, f (g⁻¹ • q) = f q := h1
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have : (g ^ ((k : ℤ) + 1)) • p = g • ((g ^ (k : ℤ)) • p) := by
        rw [show ((k : ℤ) + 1) = 1 + (k : ℤ) by ring, zpow_add, zpow_one, mul_smul]
      rw [this, hg, ih]
  | pred k ih =>
      have : (g ^ (-(k : ℤ) - 1)) • p = g⁻¹ • ((g ^ (-(k : ℤ))) • p) := by
        rw [show (-(k : ℤ) - 1) = -1 + -(k : ℤ) by ring, zpow_add, zpow_neg_one, mul_smul]
      rw [this, hginv, ih]

/-- Colorings fixed by `g` correspond to colorings of the set of cycles (orbits) of `g`. -/
