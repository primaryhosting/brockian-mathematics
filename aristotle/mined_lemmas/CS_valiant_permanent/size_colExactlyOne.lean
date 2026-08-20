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

theorem size_colExactlyOne (n : ℕ) (j : Fin n) :
    (colExactlyOne n j).size ≤ 1 + n * (5 + 3 * n) := by
  have hinner : ∀ i : Fin n,
      (Circuit.allL ((List.finRange n).map fun i' =>
        if i' = i then Circuit.const true else Circuit.not (wv n i' j))).size
        ≤ 1 + n * 3 := by
    intro i
    have := Circuit.size_allL_le
      ((List.finRange n).map fun i' =>
        if i' = i then Circuit.const true else Circuit.not (wv n i' j)) 2 ?_
    · simpa using this
    · rintro c hc
      simp only [List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨i', rfl⟩ := hc
      by_cases h : i' = i <;> simp [h, Circuit.size, wv]
  refine le_trans (Circuit.size_anyL_le _ (4 + 3 * n) ?_) ?_
  · rintro c hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨i, rfl⟩ := hc
    have := hinner i
    simp only [Circuit.size, size_wv]
    omega
  · simp only [List.length_map, List.length_finRange]
    have h5 : 1 + (4 + 3 * n) = 5 + 3 * n := by omega
    rw [h5]

