/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/
noncomputable def cdot {d : ℕ} (x y : Fin d → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (x i) * y i

/-- A finite family of vectors of `ℂ^d` is orthonormal for `QI.cdot`. -/
def IsON {d r : ℕ} (u : Fin r → (Fin d → ℂ)) : Prop :=
  ∀ k l, cdot (u k) (u l) = if k = l then 1 else 0

/-- The (unnormalized) reduced density matrix of the bipartite vector `ψ` on the first
factor: `ρ = ψ ψᴴ`. -/
noncomputable def rho {m n : ℕ} (ψ : Fin m → Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i i' => ∑ j, ψ i j * (starRingEnd ℂ) (ψ i' j)

/-- `IsSchmidt ψ σ u v` says that `ψ i j = ∑ k, σ k * u k i * v k j` is a Schmidt
decomposition of the bipartite vector `ψ`: the Schmidt coefficients `σ k` are positive reals
and the families `u`, `v` are orthonormal. -/
structure IsSchmidt {m n r : ℕ} (ψ : Fin m → Fin n → ℂ) (σ : Fin r → ℝ)
    (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ) : Prop where
  pos : ∀ k, 0 < σ k
  onu : IsON u
  onv : IsON v
  decomp : ∀ i j, ψ i j = ∑ k, (σ k : ℂ) * u k i * v k j

/-- Swapping a double sum and pulling out the factor not depending on the outer index. -/
theorem sum_swap_mul {r n : ℕ} (F : Fin r → ℂ) (G : Fin r → Fin n → ℂ) :
    ∑ j, ∑ k, F k * G k j = ∑ k, F k * ∑ j, G k j := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm

/-- Orthonormality read off with the conjugation on the second factor. -/
theorem conj_on {d r : ℕ} {v : Fin r → Fin d → ℂ} (hv : IsON v) (k l : Fin r) :
    ∑ j, v k j * (starRingEnd ℂ) (v l j) = if k = l then 1 else 0 := by
  have h1 := hv l k
  simp only [cdot] at h1
  have h2 : (∑ j, v k j * (starRingEnd ℂ) (v l j)) = ∑ j, (starRingEnd ℂ) (v l j) * v k j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h2, h1]
  by_cases hkl : k = l
  · simp [hkl]
  · simp [hkl, Ne.symm hkl]

/-- The reduced density matrix computed from a Schmidt decomposition. -/
theorem rho_eq_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) (i i' : Fin m) :
    rho ψ i i' = ∑ k, ((σ k : ℂ) ^ 2) * u k i * (starRingEnd ℂ) (u k i') := by
  show (∑ j, ψ i j * (starRingEnd ℂ) (ψ i' j)) = _
  have expand : ∀ j : Fin n, ψ i j * (starRingEnd ℂ) (ψ i' j)
      = ∑ k, ∑ l, (((σ k : ℂ) * u k i) * (starRingEnd ℂ) ((σ l : ℂ) * u l i'))
          * (v k j * (starRingEnd ℂ) (v l j)) := by
    intro j
    rw [h.decomp i j, h.decomp i' j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => expand j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_swap_mul (fun l => (((σ k : ℂ) * u k i) * (starRingEnd ℂ) ((σ l : ℂ) * u l i')))
    (fun l j => v k j * (starRingEnd ℂ) (v l j))]
  simp only [conj_on h.onv]
  simp [map_mul]
  ring

/-- The action of the reduced density matrix on a vector, in terms of a Schmidt
decomposition. -/
theorem rho_mulVec_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v)
    (w : Fin m → ℂ) (i : Fin m) :
    (rho ψ *ᵥ w) i = ∑ k, ((σ k : ℂ) ^ 2) * cdot (u k) w * u k i := by
  show (∑ i', rho ψ i i' * w i') = _
  have step : ∀ i' : Fin m, rho ψ i i' * w i'
      = ∑ k, (((σ k : ℂ) ^ 2) * u k i) * ((starRingEnd ℂ) (u k i') * w i') := by
    intro i'
    rw [rho_eq_of_isSchmidt h i i', Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun i' _ => step i',
    sum_swap_mul (fun k => ((σ k : ℂ) ^ 2) * u k i)
      (fun k i' => (starRingEnd ℂ) (u k i') * w i')]
  exact Finset.sum_congr rfl fun k _ => by rw [cdot]; ring

/-- An orthonormal family is linearly independent. -/
theorem linearIndependent_of_isON {d r : ℕ} {u : Fin r → Fin d → ℂ} (h : IsON u) :
    LinearIndependent ℂ u := by
  rw [linearIndependent_iff']
  intro s g hg l hl
  have h0 : ∀ i : Fin d, (∑ k ∈ s, g k * u k i) = 0 := by
    intro i
    have := congrFun hg i
    simpa [Finset.sum_apply] using this
  have hz : (∑ i, (starRingEnd ℂ) (u l i) * ∑ k ∈ s, g k * u k i) = 0 := by
    simp [h0]
  have hexp : (∑ i, (starRingEnd ℂ) (u l i) * ∑ k ∈ s, g k * u k i)
      = ∑ k ∈ s, g k * cdot (u l) (u k) := by
    simp only [Finset.mul_sum, cdot]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hexp] at hz
  have hz2 : (∑ k ∈ s, g k * (if l = k then (1:ℂ) else 0)) = 0 := by
    rw [show (∑ k ∈ s, g k * (if l = k then (1:ℂ) else 0))
        = ∑ k ∈ s, g k * cdot (u l) (u k) from
      Finset.sum_congr rfl fun k _ => by rw [h l k]]
    exact hz
  simpa [mul_ite, hl] using hz2

/-- `cdot` is additive/homogeneous in its second argument. -/
theorem cdot_sum {d r : ℕ} (x : Fin d → ℂ) (F : Fin r → ℂ) (y : Fin r → Fin d → ℂ) :
    cdot x (fun i => ∑ k, F k * y k i) = ∑ k, F k * cdot x (y k) := by
  simp only [cdot, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- `cdot` commutes with scalars in its second argument. -/
theorem cdot_smul {d : ℕ} (x : Fin d → ℂ) (c : ℂ) (w : Fin d → ℂ) :
    cdot x (fun i => c * w i) = c * cdot x w := by
  simp only [cdot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `cdot` is conjugate-homogeneous in its first argument. -/
theorem cdot_smul_left {d : ℕ} (x : Fin d → ℂ) (c : ℂ) (w : Fin d → ℂ) :
    cdot (fun i => c * x i) w = (starRingEnd ℂ) c * cdot x w := by
  simp only [cdot, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Contracting two vectors of `ℂ^m` against `ψ` on the first factor is computed by the
reduced density matrix. -/
theorem cdot_proj {m n : ℕ} (ψ : Fin m → Fin n → ℂ) (x y : Fin m → ℂ) :
    cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
      = cdot y (rho ψ *ᵥ x) := by
  set E : Fin m → Fin m → Fin n → ℂ := fun i i' j =>
    (x i * (starRingEnd ℂ) (ψ i j)) * ((starRingEnd ℂ) (y i') * ψ i' j) with hE
  have lhs : cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
      (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
      = ∑ i, ∑ i', ∑ j, E i i' j := by
    have step : cdot (fun j => ∑ i, (starRingEnd ℂ) (x i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (y i) * ψ i j)
        = ∑ j, ∑ i, ∑ i', E i i' j := by
      simp only [cdot, map_sum, map_mul, Complex.conj_conj, hE]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_mul_sum _ _ _ _
    rw [step, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have rhs : cdot y (rho ψ *ᵥ x) = ∑ i, ∑ i', ∑ j, E i i' j := by
    have step : cdot y (rho ψ *ᵥ x) = ∑ i', ∑ i, ∑ j, E i i' j := by
      simp only [cdot, Matrix.mulVec, dotProduct, rho, Matrix.of_apply, Finset.mul_sum,
        Finset.sum_mul, hE]
      exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    rw [step, Finset.sum_comm]
  rw [lhs, rhs]

/-- A vector of zero norm vanishes. -/
theorem eq_zero_of_cdot_self {d : ℕ} {x : Fin d → ℂ} (h : cdot x x = 0) (j : Fin d) :
    x j = 0 := by
  have hr : ((∑ j, ‖x j‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← h, cdot]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (starRingEnd ℂ) (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq (x i)]
    push_cast
    ring
  have hr' : (∑ j, ‖x j‖ ^ 2 : ℝ) = 0 := by exact_mod_cast hr
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hr' j
    (Finset.mem_univ j)
  simpa using hj

/-- For `t > 0` the `t ^ 2`-eigenspace of the reduced density matrix is spanned by the
Schmidt vectors whose Schmidt coefficient is `t`. -/
theorem eigenspace_eq_span {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) {t : ℝ} (ht : 0 < t) :
    Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2) =
      Submodule.span ℂ (Set.range (fun k : {k : Fin r // σ k = t} => u k.1)) := by
  classical
  have hon : ∀ k l, cdot (u k) (u l) = if k = l then 1 else 0 := h.onu
  have ht2 : ((t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ne_of_gt ht)
  have hmem : ∀ w : Fin m → ℂ,
      w ∈ Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2)
        ↔ ∀ i, (rho ψ *ᵥ w) i = (t : ℂ) ^ 2 * w i := by
    intro w
    rw [Module.End.mem_eigenspace_iff]
    constructor
    · intro hw i
      have := congrFun hw i
      simpa [Matrix.mulVecLin_apply] using this
    · intro hw
      funext i
      simpa [Matrix.mulVecLin_apply] using hw i
  apply le_antisymm
  · intro w hw
    rw [hmem] at hw
    set S : Finset (Fin r) := Finset.univ.filter (fun k => σ k = t) with hS
    have hmemS : ∀ x : Fin r, x ∈ S ↔ σ x = t := by
      intro x; simp [hS]
    have hc : ∀ l : Fin r, ((σ l : ℂ)) ^ 2 * cdot (u l) w = (t : ℂ) ^ 2 * cdot (u l) w := by
      intro l
      have hfun : (fun i => ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i)
          = (fun i => (t : ℂ) ^ 2 * w i) := by
        funext i
        rw [← hw i, rho_mulVec_of_isSchmidt h w i]
      have hh := congrArg (cdot (u l)) hfun
      rw [cdot_sum (u l) (fun k => ((σ k : ℂ)) ^ 2 * cdot (u k) w) u, cdot_smul] at hh
      simpa [hon, Finset.sum_ite_eq'] using hh
    have hzero : ∀ l : Fin r, σ l ≠ t → cdot (u l) w = 0 := by
      intro l hl
      have h1 := hc l
      have h2 : ((σ l : ℂ)) ^ 2 - (t : ℂ) ^ 2 ≠ 0 := by
        have hsum : σ l + t ≠ 0 := ne_of_gt (by have := h.pos l; linarith)
        have hmul : ((σ l : ℂ) - t) * ((σ l : ℂ) + t) ≠ 0 := by
          refine mul_ne_zero ?_ ?_
          · exact_mod_cast sub_ne_zero_of_ne hl
          · exact_mod_cast hsum
        intro hcon
        exact hmul (by linear_combination hcon)
      have hprod : (((σ l : ℂ)) ^ 2 - (t : ℂ) ^ 2) * cdot (u l) w = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 hprod with h' | h'
      · exact absurd h' h2
      · exact h'
    have hw' : ∀ i, w i = ∑ k ∈ S, cdot (u k) w * u k i := by
      intro i
      have e1 : (t : ℂ) ^ 2 * w i = ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i := by
        rw [← hw i, rho_mulVec_of_isSchmidt h w i]
      have e2 : ∑ k ∈ S, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i
          = ∑ k, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i := by
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro x _ hx
        have hxt : σ x ≠ t := fun hcon => hx ((hmemS x).2 hcon)
        simp [hzero x hxt]
      have e3 : ∑ k ∈ S, (((σ k : ℂ)) ^ 2 * cdot (u k) w) * u k i
          = (t : ℂ) ^ 2 * ∑ k ∈ S, cdot (u k) w * u k i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [(hmemS k).1 hk]
        ring
      exact mul_left_cancel₀ ht2 (e1.trans (e2.symm.trans e3))
    have hrepr : w = ∑ k : {k : Fin r // σ k = t}, cdot (u k.1) w • u k.1 := by
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hw' i]
      exact Finset.sum_subtype S (p := fun k => σ k = t) hmemS
        (fun k => cdot (u k) w * u k i)
    rw [hrepr]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, hmem]
    intro i
    rw [rho_mulVec_of_isSchmidt h (u k.1) i]
    have hterm : ∀ l : Fin r, ((σ l : ℂ)) ^ 2 * cdot (u l) (u k.1) * u l i
        = if l = k.1 then ((σ l : ℂ)) ^ 2 * u l i else 0 := by
      intro l
      rw [hon l k.1]
      by_cases hlk : l = k.1 <;> simp [hlk]
    rw [Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_ite_eq' Finset.univ k.1]
    simp [k.2]

/-- The number of Schmidt coefficients equal to `t > 0` is the dimension of the `t ^ 2`
eigenspace of the reduced density matrix; in particular it does not depend on the
decomposition. -/
theorem card_eq_finrank_eigenspace {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun k => σ k = t).card =
      Module.finrank ℂ (Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2)) := by
  classical
  rw [eigenspace_eq_span h ht,
    show (Set.range fun k : {k : Fin r // σ k = t} => u k.1)
      = Set.range (u ∘ (fun k : {k : Fin r // σ k = t} => k.1)) from rfl,
    finrank_span_eq_card
      ((linearIndependent_of_isON h.onu).comp (fun k : {k : Fin r // σ k = t} => k.1)
        Subtype.val_injective),
    Fintype.card_subtype]

/-- **Uniqueness of the Schmidt coefficients**: any two Schmidt decompositions of the same
bipartite vector have the same multiset of Schmidt coefficients. -/
theorem schmidt_coefficients_unique {m n r r' : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} {σ' : Fin r' → ℝ}
    {u' : Fin r' → Fin m → ℂ} {v' : Fin r' → Fin n → ℂ}
    (h : IsSchmidt ψ σ u v) (h' : IsSchmidt ψ σ' u' v') :
    Multiset.map σ Finset.univ.val = Multiset.map σ' Finset.univ.val := by
  classical
  rw [Multiset.ext]
  intro a
  rw [Multiset.count_map, Multiset.count_map]
  by_cases ha : 0 < a
  · have key : ∀ {q : ℕ} (τ : Fin q → ℝ) (x : Fin q → Fin m → ℂ) (y : Fin q → Fin n → ℂ),
        IsSchmidt ψ τ x y →
        (Multiset.filter (fun k => a = τ k) (Finset.univ : Finset (Fin q)).val).card
          = Module.finrank ℂ
              (Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((a : ℂ) ^ 2)) := by
      intro q τ x y hτ
      rw [← card_eq_finrank_eigenspace hτ ha]
      simp only [← Finset.filter_val]
      rw [← Finset.card_def]
      congr 1
      ext k
      simp [eq_comm]
    rw [key σ u v h, key σ' u' v' h']
  · have key : ∀ {q : ℕ} (τ : Fin q → ℝ), (∀ k, 0 < τ k) →
        (Multiset.filter (fun k => a = τ k) (Finset.univ : Finset (Fin q)).val).card = 0 := by
      intro q τ hpos
      rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro k _ hk
      exact ha (hk ▸ hpos k)
    rw [key σ h.pos, key σ' h'.pos]

/-- The sum of the squares of the Schmidt coefficients is the squared norm of `ψ`. -/
theorem sum_sq_of_isSchmidt {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) :
    ∑ k, σ k ^ 2 = ∑ i, ∑ j, ‖ψ i j‖ ^ 2 := by
  have hmc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  have h1 : ∑ i, rho ψ i i = ((∑ k, σ k ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl fun i _ => rho_eq_of_isSchmidt h i i, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∑ i, ((σ k : ℂ) ^ 2 * u k i * (starRingEnd ℂ) (u k i))
        = (σ k : ℂ) ^ 2 * ∑ i, (u k i * (starRingEnd ℂ) (u k i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, conj_on h.onu k k]
    simp
  have h2 : ∑ i, rho ψ i i = ((∑ i, ∑ j, ‖ψ i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [rho, Matrix.of_apply]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hmc (ψ i j)]; push_cast; ring
  exact_mod_cast h1.symm.trans h2

/-- Existence of a Schmidt decomposition. -/
theorem exists_isSchmidt {m n : ℕ} (ψ : Fin m → Fin n → ℂ) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ),
      IsSchmidt ψ σ u v := by
  classical
  have hpsd : (rho ψ).PosSemidef := by
    have hmul : rho ψ = (Matrix.of ψ) * (Matrix.of ψ)ᴴ := by
      ext i i'
      simp [rho, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hmul]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  set hA : (rho ψ).IsHermitian := hpsd.isHermitian with hAdef
  set μ : Fin m → ℝ := hA.eigenvalues with hμdef
  set b : Fin m → (Fin m → ℂ) := fun i x => (hA.eigenvectorBasis i) x with hbdef
  have hμnn : ∀ i, 0 ≤ μ i := fun i => hpsd.eigenvalues_nonneg i
  have hbon : ∀ i j, cdot (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    have hor := hA.eigenvectorBasis.orthonormal
    rw [orthonormal_iff_ite] at hor
    have h2 := hor i j
    rw [PiLp.inner_apply] at h2
    simpa [cdot, hbdef, RCLike.inner_apply, mul_comm] using h2
  have hbcomp : ∀ x y, ∑ i, b i x * (starRingEnd ℂ) (b i y) = if x = y then 1 else 0 := by
    intro x y
    have hU : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
      Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    have h2 := congrFun (congrFun hU x) y
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hbdef,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h2
  have hbeig : ∀ i x, (rho ψ *ᵥ b i) x = (μ i : ℂ) * b i x := by
    intro i x
    have h2 := congrFun (hA.mulVec_eigenvectorBasis i) x
    simpa [hbdef, hμdef, Pi.smul_apply, Complex.real_smul] using h2
  set P : Fin m → (Fin n → ℂ) := fun i j => ∑ i', (starRingEnd ℂ) (b i i') * ψ i' j with hPdef
  have hPcdot : ∀ a c, cdot (P a) (P c) = (μ a : ℂ) * (if c = a then 1 else 0) := by
    intro a c
    have hpr := cdot_proj ψ (b a) (b c)
    have hfun : (rho ψ *ᵥ b a) = fun x => (μ a : ℂ) * b a x := funext (hbeig a)
    rw [show cdot (P a) (P c) = cdot (fun j => ∑ i, (starRingEnd ℂ) (b a i) * ψ i j)
        (fun j => ∑ i, (starRingEnd ℂ) (b c i) * ψ i j) from rfl, hpr, hfun, cdot_smul, hbon c a]
  have hPzero : ∀ i, μ i = 0 → ∀ j, P i j = 0 := by
    intro i hi j
    refine eq_zero_of_cdot_self ?_ j
    rw [hPcdot i i, hi]
    simp
  set e : Fin (Fintype.card {i : Fin m // μ i ≠ 0}) ≃ {i : Fin m // μ i ≠ 0} :=
    (Fintype.equivFin {i : Fin m // μ i ≠ 0}).symm with he
  set idx : Fin (Fintype.card {i : Fin m // μ i ≠ 0}) → Fin m := fun k => (e k).1 with hidx
  have hidx_inj : Function.Injective idx := fun k l hkl => e.injective (Subtype.ext hkl)
  have hidx_pos : ∀ k, 0 < μ (idx k) := fun k => lt_of_le_of_ne (hμnn _) (Ne.symm (e k).2)
  have hsq : ∀ k, (Real.sqrt (μ (idx k))) ^ 2 = μ (idx k) := fun k => Real.sq_sqrt (hμnn _)
  have hspos : ∀ k, 0 < Real.sqrt (μ (idx k)) := fun k => Real.sqrt_pos.2 (hidx_pos k)
  have hcne : ∀ k, ((Real.sqrt (μ (idx k)) : ℂ)) ≠ 0 := by
    intro k
    exact_mod_cast ne_of_gt (hspos k)
  have hmu : ∀ k, ((μ (idx k) : ℂ)) = (Real.sqrt (μ (idx k)) : ℂ) ^ 2 := by
    intro k
    rw [show ((Real.sqrt (μ (idx k)) : ℂ)) ^ 2 = ((Real.sqrt (μ (idx k)) ^ 2 : ℝ) : ℂ) by
      push_cast; ring, hsq k]
  refine ⟨Fintype.card {i : Fin m // μ i ≠ 0}, fun k => Real.sqrt (μ (idx k)),
    fun k => b (idx k), fun k j => ((Real.sqrt (μ (idx k)) : ℂ))⁻¹ * P (idx k) j,
    hspos, ?_, ?_, ?_⟩
  · intro k l
    rw [hbon]
    by_cases hkl : k = l
    · simp [hkl]
    · have hne : idx k ≠ idx l := fun hc => hkl (hidx_inj hc)
      simp [hkl, hne]
  · intro k l
    rw [cdot_smul_left, cdot_smul, hPcdot (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, map_inv₀, Complex.conj_ofReal, hmu k]
      have hc := hcne k
      field_simp
      simp
    · have hne : idx l ≠ idx k := fun hc => hkl (hidx_inj hc).symm
      simp [hkl, hne]
  · intro i j
    have hterm : ∀ k, ((Real.sqrt (μ (idx k)) : ℂ)) * b (idx k) i *
        (((Real.sqrt (μ (idx k)) : ℂ))⁻¹ * P (idx k) j) = b (idx k) i * P (idx k) j := by
      intro k
      have hc := hcne k
      field_simp
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    have hsum1 : ∑ k, b (idx k) i * P (idx k) j
        = ∑ x : {i : Fin m // μ i ≠ 0}, b x.1 i * P x.1 j :=
      Equiv.sum_comp e (fun x : {i : Fin m // μ i ≠ 0} => b x.1 i * P x.1 j)
    have hsum2 : ∑ x : {i : Fin m // μ i ≠ 0}, b x.1 i * P x.1 j
        = ∑ i' ∈ Finset.univ.filter (fun i' => μ i' ≠ 0), b i' i * P i' j :=
      (Finset.sum_subtype (Finset.univ.filter (fun i' => μ i' ≠ 0))
        (p := fun i' => μ i' ≠ 0) (fun x => by simp) (fun i' => b i' i * P i' j)).symm
    have hsum3 : ∑ i' ∈ Finset.univ.filter (fun i' => μ i' ≠ 0), b i' i * P i' j
        = ∑ i', b i' i * P i' j := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _ hx
      have hx0 : μ x = 0 := by simpa using hx
      simp [hPzero x hx0]
    have hfin : ∑ i', b i' i * P i' j = ψ i j := by
      have e1 : ∀ i', b i' i * P i' j
          = ∑ i'', (b i' i * (starRingEnd ℂ) (b i' i'')) * ψ i'' j := by
        intro i'
        rw [hPdef, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i'' _ => by ring
      rw [Finset.sum_congr rfl fun i' _ => e1 i', Finset.sum_comm]
      have e2 : ∀ i'', ∑ i', (b i' i * (starRingEnd ℂ) (b i' i'')) * ψ i'' j
          = (if i = i'' then 1 else 0) * ψ i'' j := by
        intro i''
        rw [← Finset.sum_mul, hbcomp i i'']
      rw [Finset.sum_congr rfl fun i'' _ => e2 i'']
      simp
    rw [hsum1, hsum2, hsum3, hfin]

/-- **Schmidt decomposition.** Every bipartite pure state `ψ` (a unit vector of
`ℂ^m ⊗ ℂ^n`, written in coordinates) admits a Schmidt decomposition
`ψ i j = ∑ k, σ k * u k i * v k j` with strictly positive Schmidt coefficients `σ k`
summing (in squares) to `1` and with orthonormal families `u` and `v`; moreover the
multiset of Schmidt coefficients is uniquely determined by `ψ`. -/
theorem schmidt_decomposition {m n : ℕ} (ψ : Fin m → Fin n → ℂ)
    (hψ : ∑ i, ∑ j, ‖ψ i j‖ ^ 2 = 1) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ),
      IsSchmidt ψ σ u v ∧ ∑ k, σ k ^ 2 = 1 ∧
        ∀ (r' : ℕ) (σ' : Fin r' → ℝ) (u' : Fin r' → Fin m → ℂ) (v' : Fin r' → Fin n → ℂ),
          IsSchmidt ψ σ' u' v' → Multiset.map σ' Finset.univ.val = Multiset.map σ Finset.univ.val
    := by
  obtain ⟨r, σ, u, v, h⟩ := exists_isSchmidt ψ
  refine ⟨r, σ, u, v, h, ?_, ?_⟩
  · rw [sum_sq_of_isSchmidt h, hψ]
  · intro r' σ' u' v' h'
    exact schmidt_coefficients_unique h' h

end QI

