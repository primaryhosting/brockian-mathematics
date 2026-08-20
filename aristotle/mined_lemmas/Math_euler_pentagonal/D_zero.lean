import Mathlib
/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
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

namespace Math

/-- The smallest element of a finite set of naturals (junk value `0` if empty). -/

lemma D_zero : D 0 = {∅} := by
  ext s
  rw [mem_D_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨h0, hsum⟩
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    have h1 : a ≤ 0 :=
      hsum ▸ Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) ha
    exact h0 (by simpa [Nat.le_zero.1 h1] using ha)
  · rintro rfl
    simp

/-- **Euler's pentagonal number theorem.**

`D n` is the set of partitions of `n` into distinct positive parts (encoded as finite sets of
positive naturals with sum `n`), so the left-hand side is the coefficient of `X ^ n` in the
infinite product `∏_{i ≥ 1} (1 - X ^ i)`, the reciprocal of the partition generating function.
The right-hand side is `(-1) ^ k` if `n` is the generalized pentagonal number `k (3k - 1) / 2`
for some `k : ℤ`, and `0` otherwise. -/
