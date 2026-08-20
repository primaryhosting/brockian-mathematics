/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, but as a plain block comment: Lean 4 forbids module
-- doc comments before `import`.)

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

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the classical condition guaranteeing that the singular series
`𝔖(H)` attached to the tuple `H` does not vanish. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- `nu H p` is the number of distinct residue classes modulo `p` occupied by `H`;
it is the local datum entering the `p`-th factor of the singular series. -/
def nu (H : Finset ℕ) (p : ℕ) : ℕ :=
  (H.image (fun h : ℕ => (h : ZMod p))).card

/-- Admissibility is equivalent to the statement that `H` occupies fewer than `p`
residue classes modulo every prime `p`. -/
theorem admissible_iff_nu_lt (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → nu H p < p := by
  constructor
  · intro hA p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨r, hr⟩ := hA p hp
    have hsub : H.image (fun h : ℕ => (h : ZMod p)) ⊆ Finset.univ.erase r := by
      intro x hx
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hr h hh, Finset.mem_univ _⟩
    have h1 : nu H p ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have h2 : (Finset.univ.erase r : Finset (ZMod p)).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have h3 := hp.pos
    omega
  · intro hnu p hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    by_contra hc
    push_neg at hc
    have huniv : H.image (fun h : ℕ => (h : ZMod p)) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro r
      obtain ⟨h, hh, hcast⟩ := hc r
      exact Finset.mem_image.mpr ⟨h, hh, hcast⟩
    have := hnu p hp
    rw [nu, huniv, Finset.card_univ, ZMod.card] at this
    exact lt_irrefl _ this

/-- **Singular Series Gaps 7280.**

A new family of admissible gap ranges: if every member of a finite set `H` of
natural numbers is a prime exceeding the cardinality of `H`, then `H` is admissible,
i.e. for every prime `p` the reductions of `H` mod `p` miss some residue class.

Consequently the singular series of such a tuple has all local factors nonzero. -/
theorem SingularSeriesGaps7280 {H : Finset ℕ}
    (hprime : ∀ q ∈ H, Nat.Prime q) (hbig : ∀ q ∈ H, H.card < q) :
    Admissible H := by
  intro p hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hle : p ≤ H.card
  · -- small primes: no element of `H` is divisible by `p`, so the class `0` is missed
    refine ⟨0, ?_⟩
    intro h hh hcast
    rw [ZMod.natCast_eq_zero_iff] at hcast
    have heq : p = h := (Nat.prime_dvd_prime_iff_eq hp (hprime h hh)).mp hcast
    have := hbig h hh
    omega
  · -- large primes: `H` is too small to cover all `p` residue classes
    push_neg at hle
    have hcard : (H.image (fun h : ℕ => (h : ZMod p))).card < p :=
      lt_of_le_of_lt Finset.card_image_le hle
    have hne : H.image (fun h : ℕ => (h : ZMod p)) ≠ Finset.univ := by
      intro he
      rw [he, Finset.card_univ, ZMod.card] at hcard
      exact lt_irrefl _ hcard
    rw [Ne, Finset.eq_univ_iff_forall] at hne
    push_neg at hne
    obtain ⟨r, hr⟩ := hne
    exact ⟨r, fun h hh hcast => hr (Finset.mem_image.mpr ⟨h, hh, hcast⟩)⟩

/-- The local factor of the singular series at a prime `p` is positive for an
admissible tuple. -/
theorem singular_local_factor_pos {H : Finset ℕ} (hA : Admissible H)
    {p : ℕ} (hp : p.Prime) : 0 < 1 - (nu H p : ℝ) / p := by
  have hlt : nu H p < p := (admissible_iff_nu_lt H).mp hA p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have : (nu H p : ℝ) < p := by exact_mod_cast hlt
  have : (nu H p : ℝ) / p < 1 := (div_lt_one hp0).mpr this
  linarith

/-- Extension of the family: beyond any bound `N` (e.g. `N = 7280`) and for any
size `k` there exist admissible `k`-tuples consisting of primes larger than `N`. -/
theorem exists_admissible_beyond (k N : ℕ) :
    ∃ H : Finset ℕ, H.card = k ∧ (∀ q ∈ H, Nat.Prime q ∧ N < q) ∧ Admissible H := by
  have hinf : {q : ℕ | q.Prime ∧ max k N < q}.Infinite := by
    have h1 : {q : ℕ | q.Prime}.Infinite := Nat.infinite_setOf_prime
    have h2 : ({q : ℕ | q.Prime} \ {q : ℕ | q ≤ max k N}).Infinite :=
      h1.diff (Set.finite_le_nat _)
    refine h2.mono ?_
    intro q hq
    exact ⟨hq.1, not_le.mp hq.2⟩
  obtain ⟨H, hsub, hcard⟩ := hinf.exists_subset_card_eq k
  refine ⟨H, hcard, ?_, ?_⟩
  · intro q hq
    have := hsub hq
    simp only [Set.mem_setOf_eq] at this
    exact ⟨this.1, lt_of_le_of_lt (le_max_right k N) this.2⟩
  · refine SingularSeriesGaps7280 (fun q hq => (hsub hq).1) (fun q hq => ?_)
    have hq' := hsub hq
    simp only [Set.mem_setOf_eq] at hq'
    have : H.card ≤ max k N := by rw [hcard]; exact le_max_left k N
    exact lt_of_le_of_lt this hq'.2

/-- A concrete instance: `{11, 13, 17, 19, 23}` is an admissible 5-tuple. -/
theorem admissible_eleven_to_twentythree : Admissible {11, 13, 17, 19, 23} := by
  refine SingularSeriesGaps7280 ?_ ?_ <;> decide

#print axioms SingularSeriesGaps7280
#print axioms exists_admissible_beyond
#print axioms admissible_eleven_to_twentythree

end Brockian

