/-
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

/-!
# Ladner's theorem

This file formalises Ladner's theorem: if `P ≠ NP`, then there is an `NP`-intermediate
language, i.e. a language that lies in `NP`, is not in `P`, and is not `NP`-complete.

Since Mathlib contains no development of time-bounded computation, the classes `P`, `NP` and the
polynomial time computable functions are packaged into an abstract structure `CS.Setting`, whose
fields are the standard, model independent facts used in Ladner's proof:

* `P` is contained in `NP`;
* `P` and the polynomial time functions come with enumerations `Mdec`, `Redf` (recursive
  presentability of `P`);
* `P` is closed under finite variations, contains the empty language, and is closed downwards
  under polynomial time many-one reductions;
* `NP` is closed under intersection with a language in `P`;
* `holeEff`: for `A` in `NP`, the hole pattern of the delayed diagonalisation, i.e. the set of
  lengths `n` at which the stage function `CS.stage` is even, is decidable in polynomial time.

Only the last field depends on the machine model: it is the statement that Ladner's clocked
delayed diagonalisation can be carried out in polynomial time.  Everything else -- the
construction of the stage function, the case analysis on whether it is bounded, and the
verification of the three requirements on the resulting language -- is proved here.

The construction is Ladner's blowing-holes argument.  Given `A` in `NP` but not in `P` we build
a nondecreasing stage function `stage A Mdec Redf : ℕ → ℕ`, increasing it by one exactly when the
current requirement is met by some short string, and set
`ladnerLang s A x = A x && (stage (x.length) is even)`.  If the stage function were bounded it
would be eventually equal to some `k`: for even `k = 2 * i` the `i`-th polynomial time decider
would decide `ladnerLang s A`, which is then a finite variant of `A`, so `A` would be in `P`;
for odd `k = 2 * i + 1` the language `ladnerLang s A` would be finite (hence in `P`) while the
`i`-th polynomial time function reduces `A` to it, so again `A` would be in `P`.  Hence the
stage function is unbounded, and every even (resp. odd) stage is eventually left, which
diagonalises against every polynomial time decider (resp. against every polynomial time
reduction of `A` to `ladnerLang s A`).
-/

namespace CS

/-- Binary strings. -/
abbrev Str := List Bool

/-- A language is a decision predicate on binary strings. -/
abbrev Lang := Str → Bool

/-- `holed A t` is the language `A` with "holes" punched into it: a string `x` of length `n`
is kept only when the stage value `t n` is even. -/

lemma exists_stage_step (hub : ∀ N, ∃ n, N < stage A Mdec Redf n) (k : ℕ) :
    ∃ n, stage A Mdec Redf n = k ∧ wit A Mdec Redf (stage A Mdec Redf) n := by
  classical
  have hex : ∃ n, k < stage A Mdec Redf n := hub k
  set m := Nat.find hex with hm
  have hmspec : k < stage A Mdec Redf m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, stage_zero] at hmspec
    omega
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hple : ¬ (k < stage A Mdec Redf p) := Nat.find_min hex (by omega)
  have hstep : stage A Mdec Redf (p + 1) ≤ stage A Mdec Redf p + 1 := stage_succ_le p
  rw [hp] at hmspec
  have hpk : stage A Mdec Redf p = k := by omega
  refine ⟨p, hpk, ?_⟩
  by_contra hw
  rw [stage_succ_of_not_wit hw] at hmspec
  omega

end StageBasics

/-- An abstract axiomatisation of the ingredients of complexity theory that Ladner's theorem
needs.  All the fields are standard, model independent facts about `P`, `NP` and polynomial time
many-one reductions, except for `holeEff`, which packages the (machine model dependent)
statement that the clocked delayed diagonalisation used in Ladner's proof runs in polynomial
time. -/
structure Setting where
  /-- The class of languages decidable in polynomial time. -/
  P : Set Lang
  /-- The class of languages accepted in nondeterministic polynomial time. -/
  NP : Set Lang
  /-- The polynomial time computable functions on strings. -/
  PolyFun : Set (Str → Str)
  /-- `P ⊆ NP`. -/
  P_subset_NP : P ⊆ NP
  /-- An enumeration of polynomial time deciders. -/
  Mdec : ℕ → Lang
  /-- Every enumerated decider decides a language in `P`. -/
  Mdec_mem : ∀ i, Mdec i ∈ P
  /-- Every language in `P` occurs in the enumeration. -/
  Mdec_surj : ∀ L ∈ P, ∃ i, L = Mdec i
  /-- An enumeration of the polynomial time computable functions. -/
  Redf : ℕ → Str → Str
  /-- Every enumerated function is polynomial time computable. -/
  Redf_mem : ∀ i, Redf i ∈ PolyFun
  /-- Every polynomial time computable function occurs in the enumeration. -/
  Redf_surj : ∀ r ∈ PolyFun, ∃ i, r = Redf i
  /-- `P` is closed under finite variations. -/
  P_variant : ∀ L ∈ P, ∀ (M : Lang) (N : ℕ), (∀ x : Str, N ≤ x.length → M x = L x) → M ∈ P
  /-- The empty language is in `P`. -/
  P_empty : (fun _ => false : Lang) ∈ P
  /-- `P` is closed downwards under polynomial time many-one reductions. -/
  P_red : ∀ (A B : Lang), (∃ r ∈ PolyFun, ∀ x, A x = B (r x)) → B ∈ P → A ∈ P
  /-- `NP` is closed under intersection with a language in `P`. -/
  NP_inter_P : ∀ A ∈ NP, ∀ h ∈ P, (fun x => A x && h x : Lang) ∈ NP
  /-- Effectivity of the delayed diagonalisation: for a language in `NP`, the set of lengths at
  which Ladner's stage function is even is polynomial time decidable. -/
  holeEff : ∀ A ∈ NP,
    (fun x : Str => decide (stage A Mdec Redf x.length % 2 = 0) : Lang) ∈ P

namespace Setting

variable (s : Setting)

/-- Polynomial time many-one (Karp) reducibility. -/
