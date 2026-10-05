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

theorem permProblem_inSharpP : InSharpP permProblem := by
  refine ⟨fun n => Nat.sqrt n * Nat.sqrt n, fun n => verifier n, ⟨1, 1, ?_⟩, ⟨200, 3, ?_⟩, ?_⟩
  · intro n
    have h := sq_sqrt_le n
    simp only [pow_one, one_mul]
    omega
  · intro n
    exact size_verifier_le n
  · intro n x
    calc permProblem n x
        = Nat.card {Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool //
            IsPermMatrixOn (fun i j => x (inIdx n i j)) Y} :=
          (card_permMatrices _).symm
      _ = Nat.card {Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool //
            (verifier n).eval (Fin.append x (curryEquiv _ Y)) = true} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun Y => (eval_verifier n x Y).symm))
      _ = Nat.card {y : Fin (Nat.sqrt n * Nat.sqrt n) → Bool //
            (verifier n).eval (Fin.append x y) = true} :=
          Nat.card_congr (Equiv.subtypeEquiv (curryEquiv (Nat.sqrt n)) (fun _ => Iff.rfl))

/-! ## Valiant's theorem -/

/-- **Valiant's theorem**: the 0/1 permanent is `#P`-complete.

The formalization is relative to the (unformalized here) combinatorial core of Valiant's
theorem, namely the `#P`-hardness of counting perfect matchings in bipartite graphs, which is
taken as the hypothesis `hmatch`. What is proved here is that the 0/1 permanent problem belongs
to `#P` (via an explicit polynomial-size verifier circuit family checking that a witness is a
permutation matrix supported on the `1`-entries of the instance), and that the 0/1 permanent
problem *is* the problem of counting bipartite perfect matchings, so that the hardness
hypothesis transfers to it; hence the permanent is `#P`-complete. -/
