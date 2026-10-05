import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this formalization

Valiant's theorem states that the 0/1 permanent is `#P`-complete. This file develops:

* Boolean circuits with evaluation and size, and a definition of `#P` in its nonuniform
  circuit-verifier form (`CS.InSharpP`), of parsimonious reductions computed by
  polynomial-size circuits (`CS.ParsimoniousReduction`), and of `#P`-completeness
  (`CS.IsSharpPComplete`).
* The 0/1 permanent as a counting problem (`CS.permProblem`), its identification with
  `Matrix.permanent` of the encoded 0/1 matrix, and its identification with the problem of
  counting perfect matchings of a bipartite graph (`CS.matchingProblem`).
* A proof that the 0/1 permanent problem lies in `#P` (`CS.permProblem_inSharpP`), by an
  explicit polynomial-size verifier circuit family checking that the witness is a permutation
  matrix supported on the `1`-entries of the instance.
* `CS.valiant_permanent`: `#P`-completeness of the 0/1 permanent, given the `#P`-hardness of
  counting bipartite perfect matchings. That hardness — the combinatorial core of Valiant's
  original argument, proved there by an intricate gadget construction — is taken as an explicit
  hypothesis and is *not* formalized here.
-/

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over `N` input variables. -/
inductive BoolCircuit (N : ℕ) : Type
  | const : Bool → BoolCircuit N
  | var : Fin N → BoolCircuit N
  | neg : BoolCircuit N → BoolCircuit N
  | conj : BoolCircuit N → BoolCircuit N → BoolCircuit N
  | disj : BoolCircuit N → BoolCircuit N → BoolCircuit N

namespace BoolCircuit

variable {N : ℕ}

/-- Evaluation of a circuit on an input assignment. -/

theorem size_verifier_le (n : ℕ) : (verifier n).size ≤ 200 * (n + 1) ^ 3 := by
  have hkn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hterm : ∀ i j, (rowTerm n i j).size ≤ 5 * Nat.sqrt n + 3 := by
    intro i j
    have hb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n) 4
      ((List.finRange (Nat.sqrt n)).map
        (fun j' => BoolCircuit.disj (BoolCircuit.const (decide (j' = j)))
          (BoolCircuit.neg (yvar n i j')))) (by
          intro c hc
          simp only [List.mem_map] at hc
          obtain ⟨j', _, rfl⟩ := hc
          simp [BoolCircuit.size, yvar])
    simp only [List.length_map, List.length_finRange] at hb
    simp only [rowTerm, BoolCircuit.size]
    have hyv : (yvar n i j).size = 1 := rfl
    omega
  have hrow : ∀ i, (rowCond n i).size ≤ 1 + Nat.sqrt n * (5 * Nat.sqrt n + 4) := by
    intro i
    have hb := BoolCircuit.size_bigOr_le (N := n + Nat.sqrt n * Nat.sqrt n) (5 * Nat.sqrt n + 3)
      ((List.finRange (Nat.sqrt n)).map (fun j => rowTerm n i j)) (by
        intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact hterm i j)
    simp only [List.length_map, List.length_finRange] at hb
    simp only [rowCond]
    omega
  have hcol : ∀ j, (colCond n j).size ≤ 1 + Nat.sqrt n * 2 := by
    intro j
    have hb := BoolCircuit.size_bigOr_le (N := n + Nat.sqrt n * Nat.sqrt n) 1
      ((List.finRange (Nat.sqrt n)).map (fun i => yvar n i j)) (by
        intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨i, _, rfl⟩ := hc
        simp [BoolCircuit.size, yvar])
    simp only [List.length_map, List.length_finRange] at hb
    simp only [colCond]
    omega
  have hlen : ((List.finRange (Nat.sqrt n)).flatMap
      (fun i => (List.finRange (Nat.sqrt n)).map (fun j =>
        BoolCircuit.disj (BoolCircuit.neg (yvar n i j)) (xvar n i j)))).length
      = Nat.sqrt n * Nat.sqrt n := by
    simp [List.length_flatMap]
  have hedge : (edgeCond n).size ≤ 1 + (Nat.sqrt n * Nat.sqrt n) * 5 := by
    have hb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n) 4
      ((List.finRange (Nat.sqrt n)).flatMap
        (fun i => (List.finRange (Nat.sqrt n)).map (fun j =>
          BoolCircuit.disj (BoolCircuit.neg (yvar n i j)) (xvar n i j)))) (by
        intro c hc
        simp only [List.mem_flatMap, List.mem_map] at hc
        obtain ⟨i, _, j, _, rfl⟩ := hc
        simp [BoolCircuit.size, yvar, xvar])
    rw [hlen] at hb
    simpa [edgeCond] using hb
  have hall : ∀ c ∈ (((List.finRange (Nat.sqrt n)).map (rowCond n)) ++
      ((List.finRange (Nat.sqrt n)).map (colCond n)) ++ [edgeCond n]),
      c.size ≤ 10 * Nat.sqrt n * Nat.sqrt n + 6 * Nat.sqrt n + 3 := by
    intro c hc
    simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton,
      true_and] at hc
    rcases hc with (⟨i, rfl⟩ | ⟨j, rfl⟩) | rfl
    · have h := hrow i; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
    · have h := hcol j; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
    · have h := hedge; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
  have hvb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n)
    (10 * Nat.sqrt n * Nat.sqrt n + 6 * Nat.sqrt n + 3)
    (((List.finRange (Nat.sqrt n)).map (rowCond n)) ++
      ((List.finRange (Nat.sqrt n)).map (colCond n)) ++ [edgeCond n]) hall
  simp only [List.length_append, List.length_map, List.length_finRange,
    List.length_singleton] at hvb
  have hv : (verifier n).size ≤ 200 * (Nat.sqrt n + 1) ^ 3 := by
    rw [verifier]
    refine le_trans hvb ?_
    nlinarith [Nat.zero_le (Nat.sqrt n)]
  have hmono : (Nat.sqrt n + 1) ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  exact le_trans hv (Nat.mul_le_mul_left 200 hmono)

/-- The 0/1 permanent problem lies in `#P`. -/
