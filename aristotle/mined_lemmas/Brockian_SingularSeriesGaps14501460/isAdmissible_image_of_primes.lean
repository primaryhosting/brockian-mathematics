import Mathlib

/-!
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

namespace Brockian

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by the
finite set of integers `H`.  These are the local densities appearing in the singular
series `𝔖(H) = ∏_p (1 - nu H p / p) / (1 - 1/p)^{|H|}` of the Hardy–Littlewood
prime tuples conjecture. -/

theorem isAdmissible_image_of_primes (S : Finset ℕ)
    (hprime : ∀ q ∈ S, Nat.Prime q) (hbig : ∀ q ∈ S, S.card < q) :
    IsAdmissible (S.image (fun q : ℕ => (q : ℤ))) := by
  have hcard : (S.image (fun q : ℕ => (q : ℤ))).card = S.card :=
    Finset.card_image_of_injective _ fun a b hab => by exact_mod_cast hab
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hle : p ≤ S.card
  · -- small prime: the residue class `0` is missed
    refine nu_lt_of_missing_residue _ p 0 ?_
    intro h hh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hh
    have hq0 : ((q : ℤ) : ZMod p) = (q : ZMod p) := by push_cast; ring
    rw [hq0]
    intro hzero
    have hdvd : p ∣ q := (ZMod.natCast_eq_zero_iff q p).1 hzero
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hprime q hq)).1 hdvd
    have := hbig q hq
    omega
  · -- large prime: too few elements to cover all residues
    have h1 : nu (S.image (fun q : ℕ => (q : ℤ))) p ≤ S.card := by
      rw [nu, ← hcard]
      exact Finset.card_image_le
    omega

/-- **Singular Series Gaps 14501460.**

Inside the length-`10` window `[1450, 1460]` the three integers `1451, 1453, 1459`
form an admissible triple: every prime `p` misses at least one residue class of the
triple, so no local factor of the singular series `𝔖(H)` vanishes.  The triple has
diameter `8`, so `(0, 2, 8)` is an admissible gap pattern realised in this range. -/
