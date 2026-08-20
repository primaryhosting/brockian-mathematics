import Mathlib

set_option maxHeartbeats 1000000

/-!
# Common machinery for the Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system with Hilbert space `E`
assigns to every unit vector (equivalently, to every rank-one projection, i.e. to every
"yes/no question" about the system) a definite truth value, in a way that does not depend on
the context in which the corresponding measurement is performed, and which respects the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections — that is, in every orthonormal basis — exactly one projection is assigned the
value `true`.

We model such an assignment by a function `f : E → Bool`, the sum rule being the hypothesis
`∀ b : Fin n → E, Orthonormal ℝ b → ∃! i, f (b i) = true` (in an `n`-dimensional space an
orthonormal family indexed by `Fin n` is exactly an orthonormal basis).

This file collects the pieces used in dimensions three and four.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- "Exactly one `true`" in a triple, expressed as a count. -/

theorem ks_reduce {n : ℕ} (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool)
    (h : ∀ b : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ b → ∃! i, f (b i) = true) :
    ∃ g : E3 → Bool, ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, g (b i) = true := by
  classical
  set e : Fin n → EuclideanSpace ℝ (Fin n) := fun j => EuclideanSpace.single j (1:ℝ) with he_def
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single
  obtain ⟨k, hk, hk'⟩ := h e he
  have hn0 : 0 < n := by omega
  set φ : Fin 3 → Fin n := fun i => Equiv.swap (⟨0, hn0⟩ : Fin n) k (Fin.castLE hn i) with hφ_def
  have hφ : Function.Injective φ := fun a b hab =>
    Fin.castLE_injective hn ((Equiv.swap (⟨0, hn0⟩ : Fin n) k).injective hab)
  have hφ0 : φ 0 = k := by
    have h0 : Fin.castLE hn (0 : Fin 3) = (⟨0, hn0⟩ : Fin n) := rfl
    rw [hφ_def]
    simp only [h0, Equiv.swap_apply_left]
  set emb : E3 → EuclideanSpace ℝ (Fin n) :=
    fun u => (WithLp.toLp 2 (Function.extend φ (fun i => u i) (fun _ => (0:ℝ)))) with hemb_def
  have hemb1 : ∀ (u : E3) (i : Fin 3), (emb u) (φ i) = u i := by
    intro u i
    simp only [hemb_def, WithLp.ofLp_toLp]
    exact hφ.extend_apply _ _ i
  have hemb0 : ∀ (u : E3) (j : Fin n), (¬ ∃ i, φ i = j) → (emb u) j = 0 := by
    intro u j hj
    simp only [hemb_def, WithLp.ofLp_toLp]
    exact Function.extend_apply' _ _ _ hj
  have hinner : ∀ u v : E3, ⟪emb u, emb v⟫ = ⟪u, v⟫ := by
    intro u v
    rw [inner_en, inner_en]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image φ Finset.univ))
      (by
        intro j _ hj
        rw [hemb0 u j (by simpa using hj), zero_mul])]
    rw [Finset.sum_image (fun a _ b _ hab => hφ hab)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hemb1, hemb1])
  have hinner_e : ∀ (u : E3) (j : Fin n), (¬ ∃ i, φ i = j) → ⟪emb u, e j⟫ = 0 := by
    intro u j hj
    rw [he_def]
    simp only [EuclideanSpace.inner_single_right]
    simp [hemb0 u j hj]
  refine ⟨fun u => f (emb u), ?_⟩
  intro b hb
  set c : Fin n → EuclideanSpace ℝ (Fin n) := Function.extend φ (fun i => emb (b i)) e with hc_def
  have hc1 : ∀ i, c (φ i) = emb (b i) := fun i => hφ.extend_apply _ _ i
  have hc0 : ∀ j, (¬ ∃ i, φ i = j) → c j = e j := fun j hj => Function.extend_apply' _ _ _ hj
  have hcon : Orthonormal ℝ c := by
    rw [orthonormal_iff_ite]
    intro j1 j2
    by_cases h1 : ∃ i, φ i = j1
    · obtain ⟨i1, rfl⟩ := h1
      by_cases h2 : ∃ i, φ i = j2
      · obtain ⟨i2, rfl⟩ := h2
        rw [hc1, hc1, hinner, (orthonormal_iff_ite.mp hb) i1 i2]
        by_cases hii : i1 = i2
        · simp [hii]
        · have hne : φ i1 ≠ φ i2 := fun hc => hii (hφ hc)
          simp [hii, hne]
      · rw [hc1, hc0 j2 h2, hinner_e _ _ h2]
        have hne : φ i1 ≠ j2 := fun hcc => h2 ⟨i1, hcc⟩
        simp [hne]
    · by_cases h2 : ∃ i, φ i = j2
      · obtain ⟨i2, rfl⟩ := h2
        rw [hc0 j1 h1, hc1, real_inner_comm, hinner_e _ _ h1]
        have hne : j1 ≠ φ i2 := fun hcc => h1 ⟨i2, hcc.symm⟩
        simp [hne]
      · rw [hc0 j1 h1, hc0 j2 h2, (orthonormal_iff_ite.mp he) j1 j2]
  obtain ⟨j, hj, hju⟩ := h c hcon
  have hjrange : ∃ i, φ i = j := by
    by_contra hcon2
    rw [hc0 j hcon2] at hj
    have hjk : j = k := hk' j hj
    exact hcon2 ⟨0, by rw [hφ0, hjk]⟩
  obtain ⟨i, rfl⟩ := hjrange
  refine ⟨i, ?_, ?_⟩
  · show f (emb (b i)) = true
    rw [← hc1 i]
    exact hj
  · intro i' hi'
    have hii : φ i' = φ i := hju (φ i') (by show f (c (φ i')) = true; rw [hc1 i']; exact hi')
    exact hφ hii

end Frontier

import RequestProject.KSGeneral
import RequestProject.KS4

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

/-!
# The Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system assigns to every rank-one
projection — equivalently, to every unit vector, i.e. to every "yes/no question" about the
system — a definite truth value, independently of the context (the orthogonal resolution of
the identity) in which the corresponding measurement is performed, and compatibly with the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections, exactly one projection is assigned the value `true`.

The Kochen–Specker theorem says that no such assignment exists in dimension at least three.

Here the assignment is a Boolean-valued function `f` on the vectors of `ℝⁿ`, and the sum rule
is the requirement that for every orthonormal family `b : Fin n → EuclideanSpace ℝ (Fin n)`
— in dimension `n` such a family is precisely an orthonormal basis — there is exactly one
index `i` with `f (b i) = true`.

The dimension-three case is proved in `RequestProject.KS3` from Peres' configuration of
33 rays; `RequestProject.KSGeneral` reduces dimension `n ≥ 3` to dimension three.  The
independent four-dimensional parity proof, using the 18-vector configuration of Cabello,
Estebaranz and García-Alcaine, is in `RequestProject.KS4`.
-/

namespace Frontier

/-- **The Kochen–Specker theorem.**  In dimension `n ≥ 3` there is no noncontextual
hidden-variable assignment: no Boolean-valued function on the vectors of `ℝⁿ` selects exactly
one vector of every orthonormal basis. -/
