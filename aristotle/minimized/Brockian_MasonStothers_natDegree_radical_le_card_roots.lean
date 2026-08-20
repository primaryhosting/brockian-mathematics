import Mathlib

namespace Brockian.MasonStothers

open Polynomial UniqueFactorizationMonoid

/-
The statement as originally given (over an arbitrary field `K`, with the number of distinct
roots taken in `K` itself) is false: over `K = ℚ`, take `a = X ^ 2 + 1`, `b = 1`,
`c = X ^ 2 + 2`.  These are coprime, `a + b = c`, `a` is not constant, all are nonzero, yet
`a * b * c` has no rational root at all, so the right-hand side is `0` while the left-hand
side is `2`.  Likewise, in characteristic `p` the theorem fails (e.g. `a = X ^ p`, `b = 1`,
`c = X ^ p + 1` over `𝔽_p`).

Both defects are repaired by the standard hypotheses under which "number of distinct roots of
`a * b * c`" is the correct reading of "degree of the radical of `a * b * c`": the field is
algebraically closed and of characteristic zero.  The mathematical content (Mason–Stothers) is
unchanged.  A `DecidableEq K` instance is added since `Multiset.toFinset` requires it.
-/

/-- Over an algebraically closed field of characteristic zero, the degree of the radical of a
nonzero polynomial is bounded by its number of distinct roots (in fact they are equal). -/

lemma natDegree_radical_le_card_roots {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    [IsAlgClosed K] {p : K[X]} (hp : p ≠ 0) :
    (radical p).natDegree ≤ p.roots.toFinset.card := by
  -- Step 1: radical p splits over algebraically closed K
  have hsplits : (radical p).Splits := IsAlgClosed.splits _
  -- Step 2: natDegree (radical p) = (radical p).roots.card
  rw [hsplits.natDegree_eq_card_roots]
  -- Step 3: radical p has no repeated roots, so card = toFinset.card
  have hsf : Squarefree (radical p) := squarefree_radical
  have hnodup : (radical p).roots.Nodup := by
    rw [nodup_roots_iff_of_splits (radical_ne_zero (a := p)) hsplits]
    exact PerfectField.separable_iff_squarefree.mpr hsf
  rw [← Multiset.toFinset_card_of_nodup hnodup]
  -- radical p divides p^natDegree, so its roots are roots of p
  apply Finset.card_le_card
  -- Need: (radical p).roots.toFinset ⊆ p.roots.toFinset
  -- It suffices to show every root of radical p is a root of p
  intro x hx
  simp at hx ⊢
  refine ⟨hp, ?_⟩
  -- radical p divides p, so any root of radical p is a root of p
  have hdiv : radical p ∣ p := radical_dvd_self
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hx

/-- **Mason–Stothers** (polynomial abc): for coprime polynomials with `a + b = c`, not all
constant, `max (deg a) (deg b) (deg c)` is less than the number of distinct roots of `a * b * c`.
-/
