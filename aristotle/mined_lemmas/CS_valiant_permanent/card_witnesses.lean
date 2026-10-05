import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

lemma card_witnesses (n : ℕ) (x : Fin (n * n) → Bool) :
    Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (finProdFinEquiv (i, σ i)) = true} =
      Nat.card {y : Fin (n * n) → Bool // (permVerifier n).eval (Sum.elim x y) = true} := by
  classical
  have hmem : ∀ σ : Equiv.Perm (Fin n), (∀ i, x (finProdFinEquiv (i, σ i)) = true) →
      (permVerifier n).eval (Sum.elim x (permWitness n σ)) = true := by
    intro σ h
    rw [eval_permVerifier]
    refine ⟨fun i => ⟨σ i, by simp [permWitness_apply], fun j hj => ?_⟩,
      fun j => ⟨σ.symm j, by simp [permWitness_apply], fun i hi => ?_⟩, fun i j hij => ?_⟩
    · simp only [permWitness_apply, decide_eq_true_eq] at hj
      exact hj.symm
    · simp only [permWitness_apply, decide_eq_true_eq] at hi
      rw [← hi, Equiv.symm_apply_apply]
    · simp only [permWitness_apply, decide_eq_true_eq] at hij
      rw [← hij]
      exact h i
  refine Nat.card_eq_of_bijective
    (fun p => ⟨permWitness n p.1, hmem p.1 p.2⟩) ⟨?_, ?_⟩
  · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hst
    have hw : permWitness n σ = permWitness n τ := congrArg Subtype.val hst
    refine Subtype.ext (Equiv.ext fun i => ?_)
    have h2 := congrFun hw (finProdFinEquiv (i, σ i))
    rw [permWitness_apply, permWitness_apply] at h2
    have h3 : τ i = σ i := by simpa using h2.symm
    exact h3.symm
  · rintro ⟨y, hy⟩
    rw [eval_permVerifier] at hy
    obtain ⟨hrows, hcols, hsupp⟩ := hy
    choose f hf hfu using hrows
    have hinj : Function.Injective f := by
      intro i i' hii
      obtain ⟨i0, -, hu⟩ := hcols (f i)
      rw [hu i (hf i), hu i' (by rw [hii]; exact hf i')]
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hσ : ∀ i, σ i = f i := fun _ => rfl
    refine ⟨⟨σ, fun i => ?_⟩, ?_⟩
    · rw [hσ i]
      exact hsupp i (f i) (hf i)
    · refine Subtype.ext ?_
      funext idx
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective idx
      obtain ⟨i, j⟩ := p
      show permWitness n σ (finProdFinEquiv (i, j)) = y (finProdFinEquiv (i, j))
      rw [permWitness_apply, hσ i]
      by_cases hj : j = f i
      · rw [hj]
        simpa using (hf i).symm
      · have hy0 : y (finProdFinEquiv (i, j)) = false := by
          by_contra hcon
          exact hj (hfu i j (by simpa using hcon))
        rw [hy0, decide_eq_false]
        exact fun h => hj h.symm

/-- **The 0/1 permanent lies in `#P`.** -/
