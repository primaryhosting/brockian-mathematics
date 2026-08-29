/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

An `[[n, k, d]]_q` quantum error-correcting code is a subspace `C` of the `n`-qudit space
`(ℂ^q)^{⊗ n}`, here modelled as `EuclideanSpace ℂ (Fin n → Fin q)` (functions on the set of
classical configurations), of dimension `q ^ k`, such that every set `A` of at most `d - 1`
sites is *correctable*, i.e. satisfies the Knill–Laflamme condition
`P E P = λ(E) P` for all operators `E` supported on `A` (equivalently, for all matrix units,
which is the form used below).

The main result `QI.quantum_singleton` is the quantum Singleton bound `n - k ≥ 2 (d - 1)`.

The proof is the rank version of the standard entropic argument: for two disjoint correctable
sets `A`, `B`, writing `K` for the dimension of the code, `r_A`, `r_B` for the ranks of the
reduced density matrices on `A`, `B` and `γ` for the configuration space of the remaining
sites, one has `K * r_A ≤ |γ| * r_B` and `K * r_B ≤ |γ| * r_A`, whence `K ≤ |γ|`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open scoped ComplexConjugate
open Module (finrank)

namespace QI

noncomputable section Core

variable {X α β γ Ya Yb : Type*} [Fintype X] [Fintype α] [Fintype β] [Fintype γ]
  [Fintype Ya] [Fintype Yb]

/-- The slice of `f` along the cut `e : X ≃ α × Y` at the value `a`: the vector
`y ↦ f (e.symm (a, y))`. -/

lemma finrank_mul_cutRank_le (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X))
    (h : CorrCut e C) :
    finrank ℂ C * cutRank e C ≤ finrank ℂ (cutSpan e C) := by
  classical
  obtain ⟨lam, hlam⟩ := h
  set N := nullSp e C with hNdef
  set K := finrank ℂ ↥C with hKdef
  set r := finrank ℂ ↥(Nᗮ) with hrdef
  let bC := stdOrthonormalBasis ℂ ↥C
  let bN := stdOrthonormalBasis ℂ ↥(Nᗮ)
  set v : Fin K × Fin r → EuclideanSpace ℂ Ya :=
    fun p => psiv e ((bC p.1 : ↥C) : EuclideanSpace ℂ X) ((bN p.2 : ↥(Nᗮ)) : EuclideanSpace ℂ α)
    with hvdef
  have hmem : ∀ p, v p ∈ cutSpan e C := fun p => psiv_mem_cutSpan e C (bC p.1).2 _
  have hind : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set w : Fin K → ↥(Nᗮ) := fun i => ∑ t, conj (c (i, t)) • bN t with hwdef
    have hcoe : ∀ i, ((w i : ↥(Nᗮ)) : EuclideanSpace ℂ α)
        = ∑ t, conj (c (i, t)) • ((bN t : ↥(Nᗮ)) : EuclideanSpace ℂ α) := by
      intro i; simp [hwdef]
    have hsum : ∑ i, psiv e ((bC i : ↥C) : EuclideanSpace ℂ X)
        ((w i : ↥(Nᗮ)) : EuclideanSpace ℂ α) = 0 := by
      rw [← hc, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoe i, psiv_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [psiv_smul]
      simp [hvdef]
    have hQ : ∀ j, (∑ a, ∑ a', ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) a *
        conj (((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) a') * lam a a') = 0 := by
      intro j
      have h0 : (inner ℂ (∑ i, psiv e ((bC i : ↥C) : EuclideanSpace ℂ X)
          ((w i : ↥(Nᗮ)) : EuclideanSpace ℂ α))
          (psiv e ((bC j : ↥C) : EuclideanSpace ℂ X)
            ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α)) : ℂ) = 0 := by
        rw [hsum]; simp
      rw [sum_inner] at h0
      have hterm : ∀ i : Fin K, (inner ℂ (psiv e ((bC i : ↥C) : EuclideanSpace ℂ X)
          ((w i : ↥(Nᗮ)) : EuclideanSpace ℂ α))
          (psiv e ((bC j : ↥C) : EuclideanSpace ℂ X)
            ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α)) : ℂ)
          = (∑ a, ∑ a', ((w i : ↥(Nᗮ)) : EuclideanSpace ℂ α) a *
              conj (((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) a') * lam a a') *
            (if i = j then 1 else 0) := by
        intro i
        rw [inner_psiv e hlam (bC i).2 (bC j).2]
        congr 1
        rw [← Submodule.coe_inner]
        exact (orthonormal_iff_ite.mp bC.orthonormal) i j
      simp only [hterm, mul_ite, mul_one, mul_zero] at h0
      simpa using h0
    have hwN : ∀ j, ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) ∈ N := by
      intro j f hf
      have hnorm : (inner ℂ (psiv e f ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α))
          (psiv e f ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α)) : ℂ) = 0 := by
        rw [inner_psiv e hlam hf hf, hQ j, zero_mul]
      exact inner_self_eq_zero.mp hnorm
    have hwzero : ∀ j, w j = 0 := by
      intro j
      have hdisj := Submodule.orthogonal_disjoint N
      have : ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) = 0 := by
        have hmem2 : ((w j : ↥(Nᗮ)) : EuclideanSpace ℂ α) ∈ N ⊓ Nᗮ :=
          ⟨hwN j, (w j).2⟩
        simpa [hdisj.eq_bot] using hmem2
      exact Subtype.ext this
    intro p
    obtain ⟨j, t⟩ := p
    have h1 : ∑ t', conj (c (j, t')) • bN t' = 0 := hwzero j
    have h2 := (Fintype.linearIndependent_iff.mp bN.orthonormal.linearIndependent)
      (fun t' => conj (c (j, t'))) h1 t
    simpa using h2
  let v' : Fin K × Fin r → ↥(cutSpan e C) := fun p => ⟨v p, hmem p⟩
  have hind' : LinearIndependent ℂ v' := LinearIndependent.of_comp (cutSpan e C).subtype hind
  have hcard := hind'.fintype_card_le_finrank
  simpa [Fintype.card_prod] using hcard

/-- Restriction to the `β` factor, at a fixed value `c` of the `γ` factor. -/
