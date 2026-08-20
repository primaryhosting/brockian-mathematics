import RequestProject.Main

/-!
# A consistency witness for `CS.LadnerSetup`

`CS.ladner` is stated relative to the abstract axiomatisation `CS.LadnerSetup`.
To rule out the possibility that this package of hypotheses is contradictory
(in which case the theorem would be vacuous), we build an explicit model of it.

The model takes both classes to be the class `FC` of languages that are *finite
variations of a constant language* (equivalently: finite or cofinite sets), which
is enumerable, closed under finite variation, contains the finite languages and is
closed downwards under the reductions of the model; `SAT` is taken to be the
cofinite language `{x | x ≠ 0}`, which is complete for `FC` under those
reductions, and the clock is taken to be constant (so all four clock-semantics
fields hold trivially or vacuously).

Of course `P = NP` holds in this model, so `CS.ladner` says nothing about it; the
point of the construction is only that the hypotheses of `CS.LadnerSetup` are
jointly satisfiable, hence consistent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

namespace FinCofinModel

attribute [local instance] Classical.propDecidable

/-! ### Binary digits -/

/-- `bit n x` says that the `x`-th binary digit of `n` is `1`. -/

theorem ladnerSetup_nonempty : Nonempty LadnerSetup := ⟨FinCofinModel.model⟩

end CS

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is deliberately import-free: Lean does not allow an `import` command
-- after the header comment above, and the whole development below is elementary
-- (only natural-number arithmetic and propositional logic are needed).
-- `RequestProject/Model.lean` complements it with an explicit model of the
-- axiomatisation `CS.LadnerSetup` used here, certifying that the hypotheses are
-- consistent.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

/-- A *language* is a set of natural numbers (strings encoded as naturals),
represented as a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/--
An abstract axiomatisation of the ingredients of Ladner's theorem.

The complexity-theoretic input is packaged as explicit data together with
hypotheses.  Every hypothesis field is a statement that is a standard fact about
the real classes `P`, `NP`, polynomial-time many-one reducibility and `SAT`.

* `pEnum` is a *recursive presentation* of `P`: every polynomial-time language
  occurs in the enumeration, and nothing else does.
* `redEnum` enumerates the polynomial-time computable functions; a
  polynomial-time many-one reduction is by definition given by one of them
  (see `LadnerSetup.Reduces`).
* `clock` is Ladner's *clocked* stage function `f`.  Ladner's construction
  produces a polynomial-time computable, nondecreasing `f : Nat → Nat` whose
  associated gap set `{x | f x` is even `}` is in `P`, and which, on input `x`,
  runs a search bounded by `x` for a witness defeating the requirement of the
  current stage.  The four fields `clock_stuck_even`, `clock_stuck_odd`,
  `clock_pass_even`, `clock_pass_odd` record exactly the semantics of that
  search: if the clock gets stuck at stage `k` for ever, then the requirement of
  stage `k` has no witness at all, and if the clock passes stage `k`, then a
  witness for the requirement of stage `k` was found.

  Even stages diagonalise against membership in `P` (against `pEnum i`), odd
  stages diagonalise against reductions from `SAT` (against `redEnum i`).

No field asserts that the clock is unbounded.  That the clock *must* be unbounded
when `P ≠ NP` is the mathematical content of Ladner's argument, and it is proved
below as `LadnerSetup.clock_unbounded`.
-/
structure LadnerSetup where
  /-- The class of polynomial-time decidable languages. -/
  P : Lang → Prop
  /-- The class of languages decidable in nondeterministic polynomial time. -/
  NP : Lang → Prop
  /-- An `NP`-complete language. -/
  SAT : Lang
  /-- A recursive presentation (enumeration) of `P`. -/
  pEnum : Nat → Lang
  /-- An enumeration of the polynomial-time computable functions. -/
  redEnum : Nat → Nat → Nat
  /-- Ladner's clocked stage function. -/
  clock : Nat → Nat
  /-- `pEnum` enumerates exactly the languages of `P`. -/
  P_iff_range : ∀ A : Lang, P A ↔ ∃ i : Nat, ∀ x : Nat, (A x ↔ pEnum i x)
  /-- Deterministic polynomial time is contained in nondeterministic polynomial time. -/
  P_subset_NP : ∀ A : Lang, P A → NP A
  /-- `SAT` belongs to `NP`. -/
  SAT_mem_NP : NP SAT
  /-- `SAT` is `NP`-hard. -/
  SAT_hard : ∀ A : Lang, NP A → ∃ i : Nat, ∀ x : Nat, (A x ↔ SAT (redEnum i x))
  /-- `P` is closed downwards under polynomial-time many-one reducibility. -/
  P_reduce : ∀ A B : Lang, (∃ i : Nat, ∀ x : Nat, (A x ↔ B (redEnum i x))) → P B → P A
  /-- `P` is closed under finite variation. -/
  P_finVar : ∀ A B : Lang, P A → (∃ N : Nat, ∀ x : Nat, N ≤ x → (A x ↔ B x)) → P B
  /-- Finite (that is, bounded) languages are polynomial-time decidable. -/
  P_finite : ∀ A : Lang, (∃ N : Nat, ∀ x : Nat, N ≤ x → ¬ A x) → P A
  /-- `NP` is closed under intersection with a polynomial-time language. -/
  NP_inter_P : ∀ A B : Lang, NP A → P B → NP (fun x => A x ∧ B x)
  /-- The clock is nondecreasing. -/
  clock_mono : ∀ a b : Nat, a ≤ b → clock a ≤ clock b
  /-- The gap set of the clock is polynomial-time decidable. -/
  gap_mem_P : P (fun x => clock x % 2 = 0)
  /-- If the clock is stuck at the even stage `2 * i` from `N` on, then the search for
  a point where `pEnum i` differs from `SAT` never succeeded, i.e. there is no such
  point beyond `N`. -/
  clock_stuck_even : ∀ i N : Nat, (∀ x : Nat, N ≤ x → clock x = 2 * i) →
      ∀ x : Nat, N ≤ x → (SAT x ↔ pEnum i x)
  /-- If the clock is stuck at the odd stage `2 * i + 1` from `N` on, then the search
  for a point where the reduction `redEnum i` from `SAT` to Ladner's language fails
  never succeeded, i.e. that reduction is correct. -/
  clock_stuck_odd : ∀ i N : Nat, (∀ x : Nat, N ≤ x → clock x = 2 * i + 1) →
      ∀ x : Nat, (SAT x ↔ (SAT (redEnum i x) ∧ clock (redEnum i x) % 2 = 0))
  /-- If the clock passes the even stage `2 * i`, then a point of the gap set at which
  `pEnum i` differs from `SAT` was found. -/
  clock_pass_even : ∀ i : Nat, (∃ x : Nat, 2 * i < clock x) →
      ∃ x : Nat, clock x % 2 = 0 ∧ (SAT x ↔ ¬ pEnum i x)
  /-- If the clock passes the odd stage `2 * i + 1`, then a point at which the
  reduction `redEnum i` from `SAT` to Ladner's language fails was found. -/
  clock_pass_odd : ∀ i : Nat, (∃ x : Nat, 2 * i + 1 < clock x) →
      ∃ x : Nat, ¬ (SAT x ↔ (SAT (redEnum i x) ∧ clock (redEnum i x) % 2 = 0))

namespace LadnerSetup

variable (S : LadnerSetup)

/-- Polynomial-time many-one reducibility: `A` reduces to `B` iff some
polynomial-time computable function `redEnum i` is a many-one reduction from
`A` to `B`. -/
