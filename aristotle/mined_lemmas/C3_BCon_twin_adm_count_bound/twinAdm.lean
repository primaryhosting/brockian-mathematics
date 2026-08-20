import Mathlib
namespace C3.BCon


def twinAdm {n : ℕ} (a : ZMod n) : Prop := IsUnit a ∧ IsUnit (a + 2)

open scoped Classical in
/-- The number of residues `a` mod `n` with both `a` and `a + 2` units is at most `n`.

Type-level fix: the statement needs `Fintype (ZMod n)`, which is only available for `n ≠ 0`,
so the instance `[NeZero n]` was added (equivalent to the given hypothesis `hn : 0 < n`,
which is therefore not used in the proof but kept as requested). Decidability of the
predicate is supplied classically. -/
