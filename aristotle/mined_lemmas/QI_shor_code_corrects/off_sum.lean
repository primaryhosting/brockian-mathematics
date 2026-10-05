import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

lemma off_sum (p q : P1) (i j : Fin 9) (hc : compat p q i j = true) :
    ∑ t : T, sgnc true t * (conj (ampP p i (emb t)) * ampP q j (emb t)) = 0 := by
  cases p <;> cases q
  · -- I, I
    have h : ∀ t : T, sgnc true t * (conj (ampP I i (emb t)) * ampP I j (emb t))
        = 1 * sgnc true t := by intro t; simp [ampP_I]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- I, Z
    have h : ∀ t : T, sgnc true t * (conj (ampP I i (emb t)) * ampP Z j (emb t))
        = 1 * (sgnc true t * chi j t) := by intro t; simp [ampP_I, ampP_Z]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC2 j)
  · exact absurd hc (by simp [compat, flips])
  · -- X, X
    have h : ∀ t : T, sgnc true t * (conj (ampP X i (emb t)) * ampP X j (emb t))
        = 1 * sgnc true t := by intro t; simp [ampP_X]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · -- X, Y
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP X i (emb t)) * ampP Y i (emb t))
        = Complex.I * (sgnc true t * chi i t) := by
      intro t; rw [ampP_X, ampP_Y]; simp; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero _ _ (sC2 i)
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- Y, X
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP Y i (emb t)) * ampP X i (emb t))
        = (-Complex.I) * (sgnc true t * chi i t) := by
      intro t; rw [ampP_X, ampP_Y]; simp [chi_conj]; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero _ _ (sC2 i)
  · -- Y, Y
    have hij : i = j := by simpa [compat, flips] using hc
    subst hij
    have h : ∀ t : T, sgnc true t * (conj (ampP Y i (emb t)) * ampP Y i (emb t))
        = 1 * sgnc true t := by
      intro t
      rw [ampP_Y]
      have h2 := chi_sq i t
      simp only [map_mul, Complex.conj_I, chi_conj]
      linear_combination (sgnc true t) * h2
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ sC1
  · exact absurd hc (by simp [compat, flips])
  · -- Z, I
    have h : ∀ t : T, sgnc true t * (conj (ampP Z i (emb t)) * ampP I j (emb t))
        = 1 * (sgnc true t * chi i t) := by intro t; simp [ampP_I, ampP_Z, chi_conj]
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC2 i)
  · exact absurd hc (by simp [compat, flips])
  · exact absurd hc (by simp [compat, flips])
  · -- Z, Z
    have h : ∀ t : T, sgnc true t * (conj (ampP Z i (emb t)) * ampP Z j (emb t))
        = 1 * (sgnc true t * chi i t * chi j t) := by
      intro t; simp [ampP_Z, chi_conj]; ring
    rw [Finset.sum_congr rfl (fun t _ => h t)]
    exact sum_of_zero 1 _ (sC3 i j)

