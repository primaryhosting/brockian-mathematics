import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/

lemma exists_coeff_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (p : m → Prop)
    {x : m → 𝕜} (hx : x ∈ eigenSpan hQ p) :
    ∃ c : m → 𝕜, (∀ i, ¬ p i → c i = 0) ∧ x = ∑ i, c i • evec hQ i := by
  classical
  haveI : Fintype {i // p i} := Fintype.ofFinite _
  obtain ⟨c₀, hc₀⟩ := (mem_span_range_iff_exists_fun 𝕜).1 hx
  refine ⟨fun i => if h : p i then c₀ ⟨i, h⟩ else 0, fun i hi => by simp [hi], ?_⟩
  rw [← hc₀]
  have hsub : ∑ i ∈ Finset.univ.filter p, (fun i => (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i) i
      = ∑ i : {i // p i}, (fun i => (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i) (i : m) :=
    Finset.sum_subtype _ (by simp) _
  have hzero : ∑ i : m, (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i
      = ∑ i ∈ Finset.univ.filter p, (if h : p i then c₀ ⟨i, h⟩ else 0) • evec hQ i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi]
  rw [hzero, hsub]
  exact Finset.sum_congr rfl fun i _ => by simp [i.2]

