/-
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quadratic Reciprocity
Category: Pure Mathematics
Target: Math.quadratic_reciprocity
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

/-- **Law of quadratic reciprocity.**  For distinct odd primes `p` and `q`,
the product of the Legendre symbols `(p/q)` and `(q/p)` equals
`(-1) ^ (((p-1)/2) * ((q-1)/2))`. -/
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp1 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp2
  have hq1 : q % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq2
  have hpd : (p - 1) / 2 = p / 2 := by omega
  have hqd : (q - 1) / 2 = q / 2 := by omega
  rw [hpd, hqd]
  exact legendreSym.quadratic_reciprocity hp2 hq2 hpq

/-- The same law with primality given as ordinary hypotheses instead of instance arguments. -/
theorem quadratic_reciprocity' (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    @legendreSym q ⟨hq⟩ p * @legendreSym p ⟨hp⟩ q
      = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) :=
  @quadratic_reciprocity p q ⟨hp⟩ ⟨hq⟩ hp2 hq2 hpq

/-- Reciprocity in the case `p ≡ 3 [MOD 4]` and `q ≡ 3 [MOD 4]`: exactly one of `p`, `q` is a
quadratic residue modulo the other. -/
theorem isSquare_iff_not_isSquare_of_three_mod_four (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 3) (hq : q % 4 = 3) (hpq : p ≠ q) :
    IsSquare ((p : ZMod q)) ↔ ¬ IsSquare ((q : ZMod p)) := by
  have hpq0 : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hdvd).symm
  have hqp0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp hdvd)
  have hpc : (((p : ℤ) : ZMod q)) = (p : ZMod q) := by push_cast; ring
  have hqc : (((q : ℤ) : ZMod p)) = (q : ZMod p) := by push_cast; ring
  have hpq' : ((p : ℤ) : ZMod q) ≠ 0 := by rw [hpc]; exact hpq0
  have hqp' : ((q : ℤ) : ZMod p) ≠ 0 := by rw [hqc]; exact hqp0
  have key : legendreSym q p = -legendreSym p q :=
    legendreSym.quadratic_reciprocity_three_mod_four hp hq
  have hp1 : legendreSym q p = 1 ↔ IsSquare ((p : ZMod q)) := by
    rw [legendreSym.eq_one_iff q hpq', hpc]
  have hq1 : legendreSym p q = 1 ↔ IsSquare ((q : ZMod p)) := by
    rw [legendreSym.eq_one_iff p hqp', hqc]
  have hpv : legendreSym q p = 1 ∨ legendreSym q p = -1 :=
    (legendreSym.eq_one_or_neg_one q hpq')
  have hqv : legendreSym p q = 1 ∨ legendreSym p q = -1 :=
    (legendreSym.eq_one_or_neg_one p hqp')
  rw [← hp1, ← hq1]
  rcases hpv with h1 | h1 <;> rcases hqv with h2 | h2 <;>
    simp [h1, h2] at key ⊢

end Math

