/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Dependency graph

The goal of this file is to decompose Pollack's theorem (*the set of betrothed,
a.k.a. quasi-amicable, numbers has asymptotic density zero*) into small,
independently reusable pieces, and to prove every piece of the decomposition
that is currently within reach.  The remaining, genuinely analytic, node is
isolated as an explicit hypothesis of the main reduction theorem — it is *not*
assumed anywhere else in the file, and no axiom is added.

```
                      density_zero_reduction            (proved, conditional)
                                 ▲
                                 │
        count_betrothed_le_two_mul_count_witness        (proved)
                ▲                              ▲
                │                              │
   smaller_mem_quasiAmicableWitness     partner_injOn_betrothed   (proved)
                ▲                              ▲
                │                              │
        IsBetrothedPair.symm / partner_eq / sigma1 lemmas         (proved)

   hypothesis node (open, supplied as an argument):
        HasDensityZero quasiAmicableWitness
        i.e.  #{m ≤ x : 2m+1 < σ(m) and σ(σ(m)-m-1) = σ(m)} = o(x)
```

The hypothesis node is *weaker* than Pollack's theorem in the sense that it is a
statement about a set defined by a purely `σ`-arithmetic condition (no
existential quantifier over partners), which is the shape that the
Erdős-type machinery for amicable numbers is usually applied to.  The reduction

lemma one_lt_of_isBetrothed {n : ℕ} (h : IsBetrothed n) : 1 < n := by
  obtain ⟨m, hm, hn, hmn, h1, h2⟩ := h
  rcases Nat.lt_or_ge n 2 with h' | h'
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [sigma1_one] at h1
    omega
  · omega

/-! ## The witness set

The set of numbers satisfying the `σ`-condition enjoyed by the *smaller* member
of a betrothed pair.  It is defined without any existential quantifier over
partners, which makes it the natural target for analytic estimates. -/

/-- `quasiAmicableWitness` is the set of `m > 0` with `2m + 1 < σ(m)` and
`σ(σ(m) - m - 1) = σ(m)`.  Every smaller member of a betrothed pair lies in it. -/
