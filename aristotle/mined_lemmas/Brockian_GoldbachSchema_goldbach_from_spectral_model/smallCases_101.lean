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

/-
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace GoldbachSchema

/-- `GoldbachPair n` says that `n` is a sum of two primes. -/

lemma smallCases_101 : SmallCases 101 := by
  intro n h4 hlt hev
  obtain ⟨k, hk⟩ := hev
  have hk' : n = 2 * k := by omega
  subst hk'
  have hk1 : 2 ≤ k := by omega
  have hk2 : k ≤ 50 := by omega
  clear h4 hlt hk
  unfold GoldbachPair
  interval_cases k <;>
    first
      | exact ⟨2, 2, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 5, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 5, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 7, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 11, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 11, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 13, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 13, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 17, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 17, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨11, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨13, 19, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨13, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨17, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 23, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 29, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨23, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨29, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨31, 31, by norm_num, by norm_num, rfl⟩
      | exact ⟨29, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨31, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨37, 37, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨37, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨41, 41, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨41, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨43, 43, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨43, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨47, 47, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨47, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨53, 53, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 61, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 67, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 67, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 73, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 73, by norm_num, by norm_num, rfl⟩
      | exact ⟨19, 79, by norm_num, by norm_num, rfl⟩
      | exact ⟨5, 83, by norm_num, by norm_num, rfl⟩
      | exact ⟨3, 89, by norm_num, by norm_num, rfl⟩
      | exact ⟨7, 89, by norm_num, by norm_num, rfl⟩

/-- Monotonicity of the small-case statement in the bound. -/
