/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file develops, from first principles (no imports beyond the Lean core prelude),
a formal framework for probabilistically checkable proofs and states the PCP theorem
`NP = PCP(log n, 1)` inside it.

Design.

* Languages are predicates on binary words.
* "Efficient computability" is abstracted into a structure `CS.EffModel` carrying a
  predicate on functions (think: polynomial-time computable) together with two closure
  properties that polynomial time enjoys:
  - evaluating a (efficiently produced) local test against a candidate proof written on
    the witness tape is efficient;
  - a conjunction over all random strings of length `b n` is efficient whenever
    `2 ^ b n` is polynomially bounded (i.e. `b n = O(log n)`).
* A PCP verifier is given by an efficiently computable map sending an input `x` and a
  random string `ρ` to a *local test*: a list of at most `q` positions of the proof to
  read, together with the truth table of the predicate applied to the answers.
  Completeness is perfect and the soundness error is `1/2`, as in the standard
  definition of the class `PCP(r(n), q(n))`.

Results.

* `CS.pcp_subset_np`: unconditionally, `PCP(log n, O(1)) ⊆ NP` in any such model.
* `CS.pcp_theorem_iff`: unconditionally, the class equality `NP = PCP(log n, 1)` is
  equivalent to the inclusion `NP ⊆ PCP(log n, 1)`.
* `CS.pcp_theorem`: the class equality `NP = PCP(log n, 1)`, with the hard inclusion
  `NP ⊆ PCP(log n, 1)` (the Arora–Safra / Arora–Lund–Motwani–Sudan–Szegedy theorem,
  whose known proofs proceed by low-degree testing or by Dinur's gap amplification)
  taken as an explicit hypothesis. Everything else is proved here.
-/

namespace CS

/-- Binary words. -/
abbrev Word := List Bool

/-- A language is a set of binary words. -/
abbrev Language := Word → Prop

/-- `f` is bounded by a polynomial. -/

theorem mem_allWords {k : Nat} {w : Word} : w ∈ allWords k ↔ w.length = k := by
  induction k generalizing w with
  | zero => cases w <;> simp [allWords]
  | succ k ih =>
    constructor
    · intro h
      simp only [allWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
      obtain ⟨v, hv, h⟩ := h
      have hlen : v.length = k := ih.mp hv
      rcases h with h | h <;> subst h <;> simp [hlen]
    · intro h
      cases w with
      | nil => simp at h
      | cons b v =>
        simp only [allWords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨v, ih.mpr (by simpa using h), ?_⟩
        cases b <;> simp

/-! ### Local tests -/

/-- The index of a list of answer bits, read as a binary number (most significant first). -/
