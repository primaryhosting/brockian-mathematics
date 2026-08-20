/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no imports): a Lean module docstring
must be the first command in a file, so the required header above forces the
file to contain no `import` lines.  Everything below therefore uses only the
Lean 4 core library.  The file `RequestProject/Main.lean` re-states the results
in Mathlib terms (`∑ i ∈ Finset.Icc 1 n, f (i * d)` and `|·|`) and proves that
the two formulations agree.
-/

namespace Frontier

/-- The partial sum of `f` along the homogeneous arithmetic progression with
common difference `d`, over its first `n` terms:  `f d + f (2d) + ⋯ + f (n d)`. -/

theorem erdos_discrepancy {f : Nat → Int} (hf : IsPlusMinusOne f) :
    ∃ n d : Nat, 1 ≤ n ∧ 1 ≤ d ∧ n * d ≤ 12 ∧ 2 ≤ (hapSum f n d).natAbs := by
  refine Classical.byContradiction (fun hcon => not_discrepancy_le_one hf ?_)
  intro n d hn hd hnd
  refine Classical.byContradiction (fun hc => hcon ⟨n, d, hn, hd, hnd, ?_⟩)
  omega

/-- Reduction of the full Erdős discrepancy statement to a uniform finite
statement: if, for every `C`, there is a length `N` such that *every* `±1`
sequence has a homogeneous-AP partial sum of absolute value `> C` using only
indices `≤ N`, then every `±1` sequence has unbounded discrepancy. -/
