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

theorem matchingCount_eq_permCount {k : ℕ} (A : Fin k → Fin k → Bool) :
    matchingCount A = permCount A := by
  classical
  unfold matchingCount permCount
  refine Nat.card_congr (Equiv.ofBijective
    (β := {M : Finset (Fin k × Fin k) // IsPerfectMatching A M})
    (fun σ => ⟨Finset.image (fun i => (i, σ.1 i)) Finset.univ, ?_, ?_, ?_⟩) ?_).symm
  · rintro ⟨i, j⟩ he
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at he
    obtain ⟨a, ha1, ha2⟩ := he
    subst ha1; subst ha2
    exact σ.2 a
  · intro i
    refine ⟨σ.1 i, by simp, ?_⟩
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hy
    obtain ⟨a, ha1, ha2⟩ := hy
    subst ha1; exact ha2.symm
  · intro j
    refine ⟨σ.1.symm j, by simp, ?_⟩
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hy
    obtain ⟨a, ha1, ha2⟩ := hy
    subst ha1
    simp [← ha2]
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      refine Subtype.ext (Equiv.ext fun i => ?_)
      have hmem : (i, σ i) ∈ Finset.image (fun i => (i, τ i)) Finset.univ := by
        rw [← h]; simp
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hmem
      obtain ⟨a, ha1, ha2⟩ := hmem
      subst ha1; simp [ha2]
    · rintro ⟨M, hM1, hM2, hM3⟩
      have hg : ∀ i, ((i : Fin k), (hM2 i).choose) ∈ M := fun i => (hM2 i).choose_spec.1
      set g : Fin k → Fin k := fun i => (hM2 i).choose with hgdef
      have hinj : Function.Injective g := by
        intro a b hab
        have h1 : (a, g a) ∈ M := hg a
        have h2 : (b, g b) ∈ M := hg b
        rw [hab] at h1
        exact ((hM3 (g b)).unique h1 h2)
      have hbij : Function.Bijective g := Finite.injective_iff_bijective.mp hinj
      refine ⟨⟨Equiv.ofBijective g hbij, fun i => hM1 _ (hg i)⟩, ?_⟩
      apply Subtype.ext
      apply Finset.ext
      rintro ⟨i, j⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
        Equiv.ofBijective_apply]
      constructor
      · rintro ⟨a, rfl, rfl⟩
        exact hg a
      · intro h
        exact ⟨i, rfl, ((hM2 i).unique (hg i) h)⟩

/-- The 0/1 permanent problem evaluates `Matrix.permanent` of the encoded 0/1 matrix. -/
