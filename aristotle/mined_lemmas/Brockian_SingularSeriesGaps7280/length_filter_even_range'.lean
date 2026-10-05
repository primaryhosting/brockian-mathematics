/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- `IsPrime p` : `p` is at least `2` and has no divisor `d` with `2 ≤ d < p`. -/

theorem length_filter_even_range' (m : Nat) :
    ∀ n : Nat, ((List.range' n (2 * m)).filter (fun g => g % 2 == 0)).length = m := by
  induction m with
  | zero => intro n; simp
  | succ m ih =>
      intro n
      have hstep : 2 * (m + 1) = (2 * m) + 1 + 1 := by omega
      rw [hstep, List.range'_succ, List.range'_succ, List.filter_cons, List.filter_cons]
      have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hn with h | h
      · have h1 : ((n + 1) % 2 == 0) = false := by simp; omega
        have h2 : (n % 2 == 0) = true := by simp [h]
        rw [h1, h2]
        simpa using ih (n + 1 + 1)
      · have h1 : ((n + 1) % 2 == 0) = true := by simp; omega
        have h2 : (n % 2 == 0) = false := by simp; omega
        rw [h1, h2]
        simpa using ih (n + 1 + 1)

/-- **Singular Series Gaps 7280.**

A package of admissibility results for gap tuples, and the resulting count of admissible
gaps in every window of length `7280`:

* the pair `{0, g}` is admissible exactly when the gap `g` is even;
* the triple `{0, a, b}` is admissible exactly when `a, b` are even and `0, a, b` fail to
  cover all residues modulo `3`;
* every window `[n, n + 7280)` of gap values contains exactly `3640` admissible gaps,
  the members of the window that are picked out being precisely the admissible ones.
-/
