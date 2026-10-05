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

theorem eval_verifier (n : ℕ) (x : Fin n → Bool) (Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool) :
    (verifier n).eval (Fin.append x (curryEquiv _ Y)) = true ↔
      IsPermMatrixOn (fun i j => x (inIdx n i j)) Y := by
  classical
  set a := Fin.append x (curryEquiv (Nat.sqrt n) Y) with ha
  have hy : ∀ i j, (yvar n i j).eval a = Y i j := by
    intro i j
    simp [yvar, BoolCircuit.eval, ha, curryEquiv_apply]
  have hx : ∀ i j, (xvar n i j).eval a = x (inIdx n i j) := by
    intro i j
    simp [xvar, BoolCircuit.eval, ha]
  have hterm : ∀ i j, (rowTerm n i j).eval a = true ↔
      (Y i j = true ∧ ∀ j', j' ≠ j → Y i j' = false) := by
    intro i j
    rw [rowTerm]
    simp only [BoolCircuit.eval, Bool.and_eq_true, BoolCircuit.eval_bigAnd, List.mem_map,
      List.mem_finRange, true_and, hy]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j' hj' => ?_⟩
      have hc := h2 _ ⟨j', rfl⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        hy] at hc
      rcases hc with hc | hc
      · exact absurd hc hj'
      · exact hc
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro c ⟨j', rfl⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', hy]
      by_cases hjj : j' = j
      · exact Or.inl hjj
      · exact Or.inr (h2 j' hjj)
  have hrow : ∀ i, (rowCond n i).eval a = true ↔ ∃! j, Y i j = true := by
    intro i
    rw [rowCond, BoolCircuit.eval_bigOr]
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨c, ⟨j, rfl⟩, hc⟩
      obtain ⟨h1, h2⟩ := (hterm i j).1 hc
      refine ⟨j, h1, fun j' hj' => ?_⟩
      by_contra hne
      have hj'' : Y i j' = true := hj'
      rw [h2 j' hne] at hj''
      exact Bool.noConfusion hj''
    · rintro ⟨j, h1, h2⟩
      refine ⟨rowTerm n i j, ⟨j, rfl⟩, (hterm i j).2 ⟨h1, fun j' hj' => ?_⟩⟩
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hj' (h2 j' hc)
  have hcol : ∀ j, (colCond n j).eval a = true ↔ ∃ i, Y i j = true := by
    intro j
    rw [colCond, BoolCircuit.eval_bigOr]
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨c, ⟨i, rfl⟩, hc⟩
      exact ⟨i, by rwa [hy] at hc⟩
    · rintro ⟨i, hi⟩
      exact ⟨yvar n i j, ⟨i, rfl⟩, by rw [hy]; exact hi⟩
  have hedge : (edgeCond n).eval a = true ↔ ∀ i j, Y i j = true → x (inIdx n i j) = true := by
    rw [edgeCond, BoolCircuit.eval_bigAnd]
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro h i j hij
      have hc := h _ ⟨i, ⟨j, rfl⟩⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, Bool.not_eq_true', hy, hx, hij] at hc
      simpa using hc
    · rintro h c ⟨i, ⟨j, rfl⟩⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, Bool.not_eq_true', hy, hx]
      by_cases hij : Y i j = true
      · exact Or.inr (h i j hij)
      · exact Or.inl (by simpa using hij)
  rw [verifier, BoolCircuit.eval_bigAnd, IsPermMatrixOn]
  simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton, true_and]
  constructor
  · intro h
    exact ⟨fun i => (hrow i).1 (h _ (Or.inl (Or.inl ⟨i, rfl⟩))),
      fun j => (hcol j).1 (h _ (Or.inl (Or.inr ⟨j, rfl⟩))), hedge.1 (h _ (Or.inr rfl))⟩
  · rintro ⟨h1, h2, h3⟩ c hc
    rcases hc with (⟨i, rfl⟩ | ⟨j, rfl⟩) | rfl
    · exact (hrow i).2 (h1 i)
    · exact (hcol j).2 (h2 j)
    · exact hedge.2 h3

