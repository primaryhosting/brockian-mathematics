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

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/

theorem isRuthAaronPair_of_seed {a k : ℕ} (h : RuthAaronSeed a k) :
    IsRuthAaronPair (a * ((a + 1) * k + 1)) := by
  obtain ⟨ha, hk, hp, hq⟩ := h
  set p := (a + 1) * k + 1 with hpdef
  set q := a * k + 1 with hqdef
  have ha0 : a ≠ 0 := by omega
  have ha1 : a + 1 ≠ 0 := by omega
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hq0 : q ≠ 0 := hq.pos.ne'
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ p := hp.two_le
    calc 2 = 1 * 2 := by ring
    _ ≤ a * p := Nat.mul_le_mul ha h2
  · rw [succ_mul_seed a k, sopfr_mul ha0 hp0, sopfr_mul ha1 hq0,
      sopfr_prime hp, sopfr_prime hq, hk]
    simp only [hpdef, hqdef]
    ring

/-- The Dickson/Schinzel-type hypothesis under which we obtain infinitely many Ruth–Aaron
pairs: there are arbitrarily large `a` for which the pair of linear forms attached to
`k = sopfr (a+1) - sopfr a` takes prime values simultaneously. -/
