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

theorem card_witnesses (n : ℕ) (x : Fin n × Fin n → Bool) :
    Nat.card {w : Fin n × Fin n → Bool // (permVerifier n).eval (Sum.elim x w) = true}
      = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true} := by
  classical
  refine (Nat.card_eq_of_bijective
    (fun (σ : {σ : Equiv.Perm (Fin n) // ∀ i, x (σ i, i) = true}) =>
      (⟨fun p => decide (σ.1 p.2 = p.1), ?_⟩ :
        {w : Fin n × Fin n → Bool // (permVerifier n).eval (Sum.elim x w) = true})) ?_).symm
  · rw [eval_permVerifier]
    refine ⟨fun i => ⟨σ.1.symm i, by simp, ?_⟩, fun j => ⟨σ.1 j, by simp, ?_⟩, ?_⟩
    · intro j hj
      simp only [decide_eq_true_eq] at hj
      simp [← hj]
    · intro i hi
      simp only [decide_eq_true_eq] at hi
      exact hi.symm
    · intro i j hij
      simp only [decide_eq_true_eq] at hij
      subst hij
      exact σ.2 j
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      ext j
      have hj : τ j = σ j := by simpa using congrFun h (σ j, j)
      exact congrArg Fin.val hj.symm
    · rintro ⟨w, hw⟩
      rw [eval_permVerifier] at hw
      obtain ⟨hrow, hcol, hdom⟩ := hw
      choose g hg huniq using hcol
      have hginj : Function.Injective g := by
        intro j j' hjj
        obtain ⟨jj, _, hu⟩ := hrow (g j)
        have h1 : w (g j, j) = true := hg j
        have h2 : w (g j, j') = true := by rw [hjj]; exact hg j'
        rw [hu j h1, hu j' h2]
      have hgbij : Function.Bijective g := Finite.injective_iff_bijective.1 hginj
      refine ⟨⟨Equiv.ofBijective g hgbij, fun i => hdom _ _ (hg i)⟩, ?_⟩
      apply Subtype.ext
      funext p
      obtain ⟨i, j⟩ := p
      simp only [Equiv.ofBijective_apply]
      cases hwij : w (i, j) with
      | true => simp [huniq j i hwij]
      | false =>
          have : g j ≠ i := by
            intro h
            rw [← h] at hwij
            rw [hg j] at hwij
            exact Bool.noConfusion hwij
          simp [this]

/-! ## Size of the verifier circuit -/

