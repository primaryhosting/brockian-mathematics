/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: the required header comment
above is a module docstring, and Lean only accepts a module docstring at the
very beginning of a file when the file has no `import` commands.  Everything
below therefore uses only the Lean 4 core library.
-/

namespace CS

open Classical

/-- A language: a set of (encoded) strings, i.e. a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/-! ## Classical helpers -/


theorem exists_defeat (hcl : ∀ n, clock n ≤ n) :
    ∀ (m v : Nat), v + 1 ≤ gapF dec red K clock m →
      ∃ n, gapF dec red K clock n = v ∧ defeated dec red K clock (gapF dec red K clock) n := by
  intro m
  induction m with
  | zero =>
      intro v h
      rw [gapF_zero] at h
      omega
  | succ k ih =>
      intro v h
      by_cases hk : v + 1 ≤ gapF dec red K clock k
      · exact ih v hk
      · have hstep := gapF_succ_le dec red K clock hcl k
        have heq1 : gapF dec red K clock (k + 1) = v + 1 := by omega
        have heq0 : gapF dec red K clock k = v := by omega
        refine ⟨k, heq0, ?_⟩
        by_cases hd : defeated dec red K clock (gapF dec red K clock) k
        · exact hd
        · rw [gapF_succ dec red K clock hcl, if_neg hd] at heq1
          omega

end Construction

/-- **Ladner's theorem: if `P ≠ NP` then `NP`-intermediate languages exist.**

The statement is formulated over an abstract but faithful axiomatisation of the
relevant structure of complexity theory.  Languages are predicates on `Nat`
(strings encoded as naturals) and:

* `P` and `NP` are classes of languages with `P ⊆ NP` (`hPsubNP`);
* `dec` enumerates the polynomial-time deciders, so that `P` consists exactly
  of the languages decided by some `dec i` (`hPdec`: a recursive presentation
  of `P`);
* `red` enumerates the polynomial-time computable functions, so that `Red A B`
  (polynomial-time many-one reducibility) holds exactly when some `red i` is a
  reduction of `A` to `B` (`hRedEnum`);
* `P` contains the empty language (`hPempty`), is closed under variation on a
  bounded set of inputs (`hPfinvar`), and is closed downwards under `Red`
  (`hPdown`);
* `K` is an `NP`-complete language (`hKNP`, `hKhard`; e.g. SAT, by Cook–Levin);
* `clock` is the clock of the construction, nondecreasing, unbounded and
  bounded above by the identity (in the intended instantiation, `clock n` is
  the logarithm of `n`);
* `hGapNP` is the polynomial-time-computability input of Ladner's proof: the
  clocked gap function is polynomial-time computable, hence the language
  obtained from `K` by blowing holes along it is again in `NP`.

The conclusion is the existence of an `NP`-intermediate language: a language
`A` in `NP` which is not in `P` and which is not `NP`-hard (hence not
`NP`-complete).

The proof is Ladner's "blowing holes" diagonalisation.  The gap function is
built so that it advances to the next stage as soon as the current adversary (a
decider at an even stage, a reduction at an odd stage) has been defeated within
the clock bound.  A case split on whether the gap function is bounded then
yields the result: if it stabilises at an even stage the constructed language
is in `P` and is a bounded variant of `K`, forcing `K ∈ P`; if it stabilises at
an odd stage the constructed language is bounded, hence in `P`, while `K`
reduces to it, again forcing `K ∈ P`; and if it is unbounded every decider and
every reduction is explicitly defeated. -/
