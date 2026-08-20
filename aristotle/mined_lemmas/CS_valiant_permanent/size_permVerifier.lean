/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.PermanentGadget

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalization

The statement "the `0/1` permanent is `#P`-complete" has two halves.  What is formalized here is

* the *membership* half, in full: the `0/1` permanent is the counting function of an explicitly
  constructed family of Boolean verifier circuits of polynomial size (`InSharpP perm01Count`);
* the combinatorial identity underlying the problem: the permanent of a `0/1` matrix is the
  number of perfect matchings of the associated bipartite graph;
* the weight-elimination step of Valiant's hardness argument: restricting to `0/1` entries loses
  no generality, since every matrix of natural numbers has the same permanent as a `0/1` matrix
  of controlled size.

The remaining half of Valiant's theorem, namely the parsimonious reduction of an arbitrary `#P`
verifier to a permanent (the gadget construction), is *not* formalized here.
-/

set_option autoImplicit false

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over a set `ι` of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | const : Bool → Circuit ι
  | not : Circuit ι → Circuit ι
  | and : Circuit ι → Circuit ι → Circuit ι
  | or : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Evaluation of a circuit at a Boolean assignment of its variables. -/

theorem size_permVerifier (n : ℕ) : (permVerifier n).size ≤ 100 * (n + 1) ^ 3 := by
  have h1 : (Circuit.allL ((List.finRange n).map (rowExactlyOne n))).size
      ≤ 1 + n * (1 + (1 + n * (5 + 3 * n))) := by
    refine le_trans (Circuit.size_allL_le _ (1 + n * (5 + 3 * n)) ?_) ?_
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨i, rfl⟩ := hc
      exact size_rowExactlyOne n i
    · simp
  have h2 : (Circuit.allL ((List.finRange n).map (colExactlyOne n))).size
      ≤ 1 + n * (1 + (1 + n * (5 + 3 * n))) := by
    refine le_trans (Circuit.size_allL_le _ (1 + n * (5 + 3 * n)) ?_) ?_
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨j, rfl⟩ := hc
      exact size_colExactlyOne n j
    · simp
  have h3 := size_dominated n
  have hexp : (permVerifier n).size
      = 1 + (Circuit.allL ((List.finRange n).map (rowExactlyOne n))).size
          + (1 + (Circuit.allL ((List.finRange n).map (colExactlyOne n))).size
            + (1 + (dominated n).size + 1)) := by
    simp [permVerifier, Circuit.allL, Circuit.size]
  rw [hexp]
  have hcube : 100 * (n + 1) ^ 3 = 100 * (n ^ 3 + 3 * n ^ 2 + 3 * n + 1) := by ring
  rw [hcube]
  nlinarith [sq_nonneg n, Nat.zero_le n]

/-! ## Main theorem -/

/--
**Valiant's permanent, formalized content.**

Three statements about the `0/1` permanent:

1. it lies in (the non-uniform version of) `#P`: it is the number of witnesses accepted by an
   explicitly constructed family of Boolean verifier circuits of polynomial size;
2. it counts perfect matchings: the permanent of a `0/1` matrix is the number of permutations
   `σ` with `x (σ i, i)` for all `i`;
3. weight elimination: every matrix with natural number entries has the same permanent as a
   `0/1` matrix of controlled size, so the `0/1` case is no easier than the weighted case.

The gadget reduction showing `#P`-hardness of the permanent is not part of this formalization;
see the module docstring.
-/
