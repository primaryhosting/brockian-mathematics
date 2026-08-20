import Mathlib
namespace Brockian.Schur

/-- Bound function for the Ramsey-type induction: `fR k` many integers suffice when the
    differences take at most `k` colours. -/

def fR : ℕ → ℕ
  | 0 => 2
  | (n + 1) => (n + 1) * fR n + 2

lemma fR_pos (k : ℕ) : 0 < fR k := by
  cases k <;> simp [fR]

/-- Ramsey-type core lemma: if `A` is a finite set of naturals with at least `fR k` elements,
    all of whose positive differences receive colours in a set `S` of size `k`, then `A`
    contains `a < b < d` with `c (b-a) = c (d-b) = c (d-a)`. -/
