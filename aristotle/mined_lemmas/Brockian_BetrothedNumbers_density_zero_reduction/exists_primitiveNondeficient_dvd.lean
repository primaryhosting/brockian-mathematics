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

lemma exists_primitiveNondeficient_dvd {n : ℕ} (hn : Nondeficient n) (hpos : 0 < n) :
    ∃ d, d ∣ n ∧ PrimitiveNondeficient d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hprim : ∀ d, d ∣ n → d < n → ¬ Nondeficient d
    · exact ⟨n, dvd_rfl, ⟨hn, hprim⟩⟩
    · push_neg at hprim
      obtain ⟨d, hdvd, hlt, hd⟩ := hprim
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | h
        · simp [Nondeficient, sigma1_zero] at hd
          omega
        · exact h
      obtain ⟨e, he, hprime⟩ := ih d hlt hd hdpos
      exact ⟨e, he.trans hdvd, hprime⟩

/-! ## The reduction -/

/-- The partner map is injective on betrothed numbers. -/
