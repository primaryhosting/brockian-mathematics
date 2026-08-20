import Mathlib
/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Ladner's theorem

If `P ≠ NP`, then there is an `NP`-intermediate language: a language in `NP` that is
neither in `P` nor `NP`-complete.

Mathlib has no development of computational complexity, so the ambient complexity-theoretic
setting is packaged into the structure `CS.Model` below: it fixes the classes `P` and `NP`
(as sets of languages, a language being a set of natural numbers viewed as encoded strings),
a length function, an effective enumeration `dec` of the polynomial-time decision procedures
and an effective enumeration `red` of the polynomial-time functions (used to define
polynomial-time many-one reducibility), together with the standard closure properties of
these classes.

Everything in the proof of `CS.ladner` — the delayed-diagonalization construction
(`CS.Model.stage`, defined by well-founded recursion) and all its properties — is carried out
from these data.  The one remaining machine-model fact is supplied as the explicit hypothesis
`hstage` of `CS.ladner`: the "hole" set `{x | Even (stage L (len x))}` determined by the stage
function lies in `P`.  This is the routine clock/bookkeeping part of Ladner's argument: the
witness search performed at stage `n` only inspects inputs of length at most `log₂ log₂ n`
(see `CS.Model.Wit`), so the values `stage L 0, …, stage L n` can be tabulated in time
polynomial in `n`.
-/

namespace CS

open scoped Classical

/-- A language is a set of (encoded) inputs. -/
abbrev Lang : Type := Set ℕ

/-- The complexity-theoretic data the argument runs on: the classes `P` and `NP`, a length
function on encoded inputs, effective enumerations of polynomial-time deciders and of
polynomial-time functions, and the standard closure properties. -/
structure Model where
  /-- The class `P`. -/
  P : Set Lang
  /-- The class `NP`. -/
  NP : Set Lang
  /-- Length of an encoded input. -/
  len : ℕ → ℕ
  /-- `dec i` is the decision procedure of the `i`-th polynomial-time machine. -/
  dec : ℕ → ℕ → Bool
  /-- `red i` is the `i`-th polynomial-time computable function. -/
  red : ℕ → ℕ → ℕ
  /-- There are only finitely many inputs of any given length. -/
  len_finite : ∀ t : ℕ, {x : ℕ | len x ≤ t}.Finite
  /-- `P` is exactly the class of languages decided by the enumerated machines. -/
  P_eq : ∀ A : Lang, A ∈ P ↔ ∃ i, ∀ x, x ∈ A ↔ dec i x = true
  /-- `P ⊆ NP`. -/
  P_subset_NP : P ⊆ NP
  /-- `NP` is closed under intersection with languages in `P`. -/
  NP_inter_P : ∀ A ∈ NP, ∀ B ∈ P, A ∩ B ∈ NP
  /-- Finite languages are in `P`. -/
  P_of_finite : ∀ A : Lang, A.Finite → A ∈ P
  /-- `P` is closed under finite variation. -/
  P_of_finite_symmDiff : ∀ A ∈ P, ∀ B : Lang, {x | ¬ (x ∈ A ↔ x ∈ B)}.Finite → B ∈ P
  /-- `P` is closed downwards under polynomial-time many-one reductions. -/
  P_red_closed : ∀ A B : Lang, (∃ i, ∀ x, x ∈ A ↔ red i x ∈ B) → B ∈ P → A ∈ P
  /-- Polynomial-time functions have polynomially bounded output length. -/
  red_poly : ∀ i, ∃ c, ∀ x, len (red i x) ≤ c * (len x + 1) ^ c

namespace Model

variable (M : Model)

/-- Polynomial-time many-one reducibility `A ≤ₚ B`. -/

def Mism (L : Lang) (F : ℕ → ℕ) (k x : ℕ) : Prop :=
  if k % 2 = 0 then
    ¬ ((x ∈ L ∧ Even (F (M.len x))) ↔ M.dec (k / 2) x = true)
  else
    ¬ ((x ∈ L) ↔ (M.red (k / 2) x ∈ L ∧ Even (F (M.len (M.red (k / 2) x)))))

/-- Requirement `k` has a witness found by stage `n`: the search only inspects inputs `x`
of length at most `llog n` whose image under the relevant reduction also has length at most
`llog n`. -/
