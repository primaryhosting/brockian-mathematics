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

lemma wit_congr {t t' : ℕ → ℕ} {n : ℕ} (h : ∀ m ≤ n, t m = t' m) :
    wit A Mdec Redf t n ↔ wit A Mdec Redf t' n := by
  have hn : t n = t' n := h n le_rfl
  have hh : ∀ x : Str, x.length ≤ Nat.log 2 (n + 1) → holed A t x = holed A t' x := by
    intro x hx
    simp only [holed, h x.length (le_trans hx (log_two_succ_le n))]
  unfold wit
  rw [hn]
  by_cases hpar : t' n % 2 = 0
  · rw [if_pos hpar, if_pos hpar]
    constructor <;> rintro ⟨x, hx, hne⟩ <;> refine ⟨x, hx, ?_⟩
    · rw [← hh x hx]; exact hne
    · rw [hh x hx]; exact hne
  · rw [if_neg hpar, if_neg hpar]
    constructor <;> rintro ⟨x, hx, hr, hne⟩ <;> refine ⟨x, hx, hr, ?_⟩
    · rw [← hh _ hr]; exact hne
    · rw [hh _ hr]; exact hne

