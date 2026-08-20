import Mathlib
namespace C4.ST2

/-- The power set of a finite type of cardinality `n` has `2 ^ n` elements. -/

theorem no_surj_powerset {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- The universal set of `α` is countable iff `α` embeds into `ℕ`.

The original statement had the right-hand side `Nonempty (α ↪ ℕ) → True`, which is
trivially true and hence made the claim false for uncountable `α`; the intended
right-hand side `Nonempty (α ↪ ℕ)` is used instead. -/
