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

theorem card_permMatrices {k : ℕ} (X : Fin k → Fin k → Bool) :
    Nat.card {Y : Fin k → Fin k → Bool // IsPermMatrixOn X Y} = permCount X := by
  classical
  unfold permCount
  refine Nat.card_congr (Equiv.ofBijective
    (β := {Y : Fin k → Fin k → Bool // IsPermMatrixOn X Y})
    (fun σ => ⟨fun i j => decide (σ.1 i = j), ?_, ?_, ?_⟩) ?_).symm
  · intro i
    refine ⟨σ.1 i, by simp, ?_⟩
    intro y hy
    simpa [eq_comm] using hy
  · intro j
    exact ⟨σ.1.symm j, by simp⟩
  · intro i j hij
    simp only [decide_eq_true_eq] at hij
    subst hij
    exact σ.2 i
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      refine Subtype.ext (Equiv.ext fun i => ?_)
      have hval := congrFun (congrFun h i) (σ i)
      simp at hval
      exact hval.symm
    · rintro ⟨Y, hY1, hY2, hY3⟩
      set g : Fin k → Fin k := fun i => (hY1 i).choose with hgdef
      have hgY : ∀ i, Y i (g i) = true := fun i => (hY1 i).choose_spec.1
      have huniq : ∀ i j, Y i j = true → j = g i := fun i j h => (hY1 i).choose_spec.2 j h
      have hsurj : Function.Surjective g := by
        intro j
        obtain ⟨i, hi⟩ := hY2 j
        exact ⟨i, (huniq i j hi).symm⟩
      have hbij : Function.Bijective g := Finite.surjective_iff_bijective.mp hsurj
      refine ⟨⟨Equiv.ofBijective g hbij, fun i => hY3 i (g i) (hgY i)⟩, ?_⟩
      apply Subtype.ext
      funext i j
      simp only [Equiv.ofBijective_apply]
      by_cases h : Y i j = true
      · have hj := huniq i j h
        simp [hj, hgY]
      · simp only [Bool.not_eq_true] at h
        have hne : g i ≠ j := by
          intro hc
          rw [← hc] at h
          rw [hgY i] at h
          exact Bool.noConfusion h
        simp [h, hne]

