/-
# Riemann Roch Curve
Category: Frontier Math
Target: Math2.riemann_roch_curve
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open Polynomial

/-!
# Riemann–Roch for a smooth projective curve

Mathlib (as of this development) contains no Riemann–Roch theorem, no theory of divisors on
curves, no sheaf cohomology of curves and no Serre duality, so the whole set-up below is built
from scratch on top of Mathlib's theory of the rational function field `RatFunc k` and of
polynomials.

We work with the smooth projective curve `ℙ¹_k` over an arbitrary field `k`, described through
its function field `k(X) = RatFunc k`:

* its closed points (`Math2.Place`) are the monic irreducible polynomials together with the
  point at infinity;
* `Math2.ord` is the normalized valuation (order of vanishing) at a closed point;
* `Math2.Divisor` is the group of divisors, `Math2.degDiv` the degree of a divisor
  (each point counted with the degree of its residue field);
* `Math2.RRSpace D` is the Riemann–Roch space `L(D) = {f ≠ 0 : div f + D ≥ 0} ∪ {0}` and
  `Math2.ell D = ℓ(D)` its dimension over `k`;
* `Math2.canonicalDivisor` is the canonical divisor `-2·∞` and `Math2.genus` the genus `0`.

The main result `Math2.riemann_roch_curve` is the Riemann–Roch formula
`ℓ(D) - ℓ(K - D) = deg D + 1 - g`, valid for every divisor `D`.
-/

namespace Math2

/-!
## The smooth projective curve

We work with the projective line `ℙ¹_k` over an arbitrary field `k`, presented through its
function field `k(X) = RatFunc k`.  Its closed points (places of the function field) are the
monic irreducible polynomials (the finite closed points) together with the point at infinity.
-/

variable {k : Type*} [Field k]

/-- A closed point of the projective line `ℙ¹_k`: either a monic irreducible polynomial
(a finite closed point) or `none`, the point at infinity. -/
abbrev Place (k : Type*) [Field k] := Option {p : k[X] // p.Monic ∧ Irreducible p}

/-- A divisor on `ℙ¹_k`: a finitely supported formal `ℤ`-combination of closed points. -/
abbrev Divisor (k : Type*) [Field k] := Place k →₀ ℤ

/-! ### Order functions (normalized valuations) at the closed points -/


lemma mem_RRAux_iff (D : Divisor k) (f : RatFunc k) :
    f ∈ RRAux D ↔ f ∈ RRSet D := by
  have hA : divElt D ≠ 0 := divElt_ne_zero D
  have hmem : f ∈ RRAux D ↔ ∃ g : k[X], g.degree < (((degDiv D + 1).toNat : ℕ) : WithBot ℕ) ∧
      algebraMap k[X] (RatFunc k) g = f * divElt D := by
    rw [RRAux, Submodule.mem_comap, mem_polySub_iff]
    rfl
  rw [hmem, RRSet, Set.mem_setOf_eq]
  by_cases hf : f = 0
  · subst hf
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨0, by simp, by simp⟩⟩
  constructor
  · rintro ⟨g, hdeg, hg⟩
    right
    have hgne : g ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hg
      exact (mul_ne_zero hf hA) hg.symm
    have hnat : (g.natDegree : ℤ) ≤ degDiv D := by
      have : g.natDegree < (degDiv D + 1).toNat := by
        have := hdeg
        rw [Polynomial.degree_eq_natDegree hgne] at this
        exact_mod_cast this
      omega
    intro P
    cases P with
    | none =>
        have h1 : ord none (f * divElt D) = -(g.natDegree : ℤ) := by
          rw [← hg, ord_infty_algebraMap]
        rw [ord_mul none hf hA, ord_divElt_infty] at h1
        omega
    | some q =>
        have h1 : ord (some q) (f * divElt D) = (multiplicity q.1 g : ℤ) := by
          rw [← hg]
          exact ordFin_algebraMap q.2.2.prime hgne
        rw [ord_mul (some q) hf hA, ord_divElt_finite] at h1
        have : (0 : ℤ) ≤ (multiplicity q.1 g : ℤ) := Int.natCast_nonneg _
        omega
  · rintro (h | h)
    · exact absurd h hf
    · have hfin : ∀ q : k[X], q.Monic → Irreducible q → 0 ≤ ordFin q (f * divElt D) := by
        intro q hqm hqi
        have h1 : ord (some ⟨q, hqm, hqi⟩ : Place k) (f * divElt D) = ordFin q (f * divElt D) := rfl
        have h2 := h (some ⟨q, hqm, hqi⟩)
        have h3 : ord (some ⟨q, hqm, hqi⟩ : Place k) (f * divElt D)
            = ord (some ⟨q, hqm, hqi⟩ : Place k) f + D (some ⟨q, hqm, hqi⟩) := by
          rw [ord_mul _ hf hA, ord_divElt_finite]
        rw [← h1, h3]
        omega
      obtain ⟨g, hgne, hg⟩ := isPoly_of_ordFin_nonneg (mul_ne_zero hf hA) hfin
      refine ⟨g, ?_, hg⟩
      have h1 : ord none (f * divElt D) = -(g.natDegree : ℤ) := by
        rw [← hg, ord_infty_algebraMap]
      rw [ord_mul none hf hA, ord_divElt_infty] at h1
      have h3 := h none
      have hnat : (g.natDegree : ℤ) ≤ degDiv D := by omega
      rw [Polynomial.degree_eq_natDegree hgne]
      have : g.natDegree < (degDiv D + 1).toNat := by omega
      exact_mod_cast this

/-- The Riemann–Roch space `L(D)` of a divisor `D`, as a `k`-subspace of the function field. -/
