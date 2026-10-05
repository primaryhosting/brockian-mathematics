/-
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The header above is repeated verbatim as the module docstring, since Lean does
not allow a doc comment to precede the import line.
-/

namespace Brockian.BetrothedNumbers.Dynamics

open ArithmeticFunction

/-- The *quasi-aliquot* (or "betrothed partner") function
`partner n = σ₁(n) - n - 1`, i.e. the sum of the proper divisors of `n`
excluding `1` (and excluding `n` itself).  Subtraction is truncated
subtraction on `ℕ`; for `n ≥ 2` we always have `n + 1 ≤ σ₁(n)`, so no
truncation occurs there. -/
def partner (n : ℕ) : ℕ := sigma 1 n - n - 1

/-- `m` and `n` form a *betrothed (quasi-amicable) pair*: they are distinct
positive integers, each of which has the other as the sum of its proper
divisors excluding `1`; equivalently `σ₁(m) = σ₁(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- A *nontrivial positive 2-cycle* of `partner`: distinct positive `m`, `n`
with `partner m = n` and `partner n = m`. -/
def IsNontrivialTwoCycle (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ partner m = n ∧ partner n = m

/-- Small helper: `partner n = m` together with `0 < m` is exactly
`σ₁(n) = n + m + 1` (truncation of `ℕ`-subtraction is harmless here). -/
lemma partner_eq_iff_sigma_eq {m n : ℕ} (hm : 0 < m) :
    partner n = m ↔ sigma 1 n = n + m + 1 := by
  unfold partner
  omega

/-- **Betrothed pairs are exactly the nontrivial positive 2-cycles of
`partner (n) = σ₁(n) - n - 1`.** -/
theorem isBetrothedPair_iff_nontrivial_twoCycle (m n : ℕ) :
    IsBetrothedPair m n ↔ IsNontrivialTwoCycle m n := by
  constructor
  · rintro ⟨hm, hn, hmn, hsm, hsn⟩
    refine ⟨hm, hn, hmn, ?_, ?_⟩
    · rw [partner_eq_iff_sigma_eq hn]; omega
    · rw [partner_eq_iff_sigma_eq hm]; omega
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    rw [partner_eq_iff_sigma_eq hn] at h1
    rw [partner_eq_iff_sigma_eq hm] at h2
    exact ⟨hm, hn, hmn, by omega, by omega⟩

end Brockian.BetrothedNumbers.Dynamics

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

