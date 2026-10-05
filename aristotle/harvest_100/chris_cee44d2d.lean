import Mathlib

/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
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


namespace Math2

/-- The set of dimensions that can support a framed manifold of Kervaire invariant one,
according to the Browder / Hill–Hopkins–Ravenel constraints: `n = 2 ^ k - 2`
with `2 ≤ k ≤ 7`. -/
def KervaireDimension (n : ℕ) : Prop := ∃ k, 2 ≤ k ∧ k ≤ 7 ∧ n + 2 = 2 ^ k

/-- The admissible Kervaire dimensions are exactly `2, 6, 14, 30, 62, 126`. -/
theorem kervaireDimension_iff (n : ℕ) :
    KervaireDimension n ↔ n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  constructor
  · rintro ⟨k, hk2, hk7, hn⟩
    interval_cases k <;> norm_num at hn <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩,
      ⟨6, by norm_num⟩, ⟨7, by norm_num⟩]

/--
**Kervaire invariant one dimensions** (Hill–Hopkins–Ravenel; statement form).

Let `KervaireInvariantOne n` be any predicate on dimensions (intended: there exists a
smooth framed `n`-manifold of Kervaire invariant one).  Browder's theorem says such a
dimension must be of the form `n = 2 ^ k - 2` with `k ≥ 2`, and the
Hill–Hopkins–Ravenel theorem says that in that case `k ≤ 7`.  Given these two inputs,
the only possible dimensions are the six values `2, 6, 14, 30, 62, 126`; in particular
the Kervaire invariant vanishes in every other dimension.
-/
theorem kervaire_invariant (KervaireInvariantOne : ℕ → Prop)
    (browder : ∀ n, KervaireInvariantOne n → ∃ k, 2 ≤ k ∧ n + 2 = 2 ^ k)
    (hhr : ∀ n k, KervaireInvariantOne n → n + 2 = 2 ^ k → k ≤ 7) :
    ∀ n, KervaireInvariantOne n →
      n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  intro n hn
  obtain ⟨k, hk2, hk⟩ := browder n hn
  exact (kervaireDimension_iff n).1 ⟨k, hk2, hhr n k hn hk, hk⟩

end Math2

