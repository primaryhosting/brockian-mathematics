/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A list `H` of shifts (a *k*-tuple, with `k = H.length`) is **admissible** if for every
prime `p` the shifts do not cover all residue classes modulo `p`: there is a residue
class `a < p` avoided by `h % p` for every `h ∈ H`.

This is the classical admissibility condition from the Hardy–Littlewood prime `k`-tuple
conjecture: it is exactly the condition preventing the pattern `n + h`, `h ∈ H`, from being
forced to contain a multiple of some prime. -/
def Admissible (H : List Nat) : Prop :=
  ∀ p : Nat, IsPrimeNat p → ∃ a : Nat, a < p ∧ ∀ h ∈ H, h % p ≠ a

/-- All primes `p ≤ 8` (indeed all moduli `2 ≤ q < 9`) miss some residue class of
`(0, 2, 6, 8)`; a finite check. -/
theorem missed_residue_small : ∀ q < 9, 2 ≤ q → ∃ a < q, ∀ h ∈ [0, 2, 6, 8], h % q ≠ a := by
  decide

/-- For a modulus `q ≥ 9` the residue class `1` is avoided, since each shift is `< q`
and none of them equals `1`. -/
theorem missed_residue_large (q : Nat) (hq : 9 ≤ q) :
    ∃ a < q, ∀ h ∈ [0, 2, 6, 8], h % q ≠ a := by
  refine ⟨1, by omega, ?_⟩
  intro h hh
  have hlt : h < q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl <;> omega
  rw [Nat.mod_eq_of_lt hlt]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl <;> omega

/-- **Admissibility for `4`-tuples**: the prime `4`-tuple pattern `(0, 2, 6, 8)` is
admissible, i.e. for every prime `p` some residue class modulo `p` is avoided by all of
`0, 2, 6, 8`. -/
theorem AdmissibilityKTupleK4 : Admissible [0, 2, 6, 8] := by
  intro p hp
  have h2 : 2 ≤ p := hp.1
  by_cases hle : p < 9
  · obtain ⟨a, ha, hall⟩ := missed_residue_small p hle h2
    exact ⟨a, ha, hall⟩
  · obtain ⟨a, ha, hall⟩ := missed_residue_large p (by omega)
    exact ⟨a, ha, hall⟩

end Brockian

/-
Mathlib companion to `RequestProject/AdmissibilityKTupleK4.lean`.

Restates admissibility of the 4-tuple `(0, 2, 6, 8)` using Mathlib's `Nat.Prime`
and `ZMod p`, and derives it from the self-contained core statement
`Brockian.AdmissibilityKTupleK4`.
-/
import Mathlib
import RequestProject.AdmissibilityKTupleK4

namespace Brockian

/-- Mathlib's primality implies the primality notion used in the core file. -/
theorem isPrimeNat_of_prime {p : ℕ} (hp : p.Prime) : IsPrimeNat p :=
  ⟨hp.two_le, fun d hd => (Nat.Prime.eq_one_or_self_of_dvd hp d hd)⟩

/-- Admissibility of the `4`-tuple `(0, 2, 6, 8)`, phrased with `ZMod p`:
for every prime `p` there is a residue class in `ZMod p` hit by none of the shifts. -/
theorem admissibility_kTuple_k4_zmod (p : ℕ) (hp : p.Prime) :
    ∃ a : ZMod p, ∀ h ∈ ({0, 2, 6, 8} : Finset ℕ), (h : ZMod p) ≠ a := by
  obtain ⟨a, ha, hall⟩ := AdmissibilityKTupleK4 p (isPrimeNat_of_prime hp)
  refine ⟨(a : ZMod p), ?_⟩
  intro h hh hcast
  have hmem : h ∈ [0, 2, 6, 8] := by
    fin_cases hh <;> simp
  have := hall h hmem
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha] at hcast
  exact this hcast

end Brockian

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

