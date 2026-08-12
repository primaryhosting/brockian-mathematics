/-
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Finite-dimensional Stinespring dilation theorem: every completely positive
trace-preserving (CPTP) linear map on matrix algebras can be realised by
adjoining an ancilla in a fixed pure state, applying a unitary on the enlarged
system, and tracing out the environment.

The main result is `QI.stinespring`. Along the way we prove Choi's theorem
(`QI.choi_posSemidef`), the Kraus decomposition of a completely positive map
(`QI.exists_kraus`), the completeness relation for the Kraus operators of a
trace-preserving map (`QI.kraus_sum_eq_one`), and the extension of an isometry
to a unitary (`QI.exists_unitary_extension`).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QI

variable {A B : Type*}

/-- The partial trace of a matrix on a bipartite system `B ⊗ E` over the second
(environment) factor. -/
noncomputable def ptrace {B E : Type*} [Fintype E] (M : Matrix (B × E) (B × E) ℂ) :
    Matrix B B ℂ :=
  fun a b => ∑ s, M (a, s) (b, s)

/-- The ampliation `id_K ⊗ Φ` of a linear map `Φ` between matrix algebras:
it acts as `Φ` on the second tensor factor and as the identity on the first. -/
def ampliate (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (K : Type*)
    (ρ : Matrix (K × A) (K × A) ℂ) : Matrix (K × B) (K × B) ℂ :=
  fun p q => Φ (fun i j => ρ (p.1, i) (q.1, j)) p.2 q.2

/-- A linear map between matrix algebras is *completely positive* when all of its
ampliations `id_{Fin k} ⊗ Φ` map positive semidefinite matrices to positive
semidefinite matrices. -/
def IsCompletelyPositive (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ (k : ℕ) (ρ : Matrix (Fin k × A) (Fin k × A) ℂ), ρ.PosSemidef →
    (ampliate Φ (Fin k) ρ).PosSemidef

/-- A linear map between matrix algebras is *trace preserving* when it preserves traces. -/
def IsTracePreserving [Fintype A] [Fintype B] (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Prop :=
  ∀ ρ : Matrix A A ℂ, (Φ ρ).trace = ρ.trace

private lemma sum_comm₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) : ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The Choi matrix of a linear map between matrix algebras. -/
def choi [Fintype A] [DecidableEq A] [Fintype B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => Φ (single p.1 q.1 1) p.2 q.2

/-- Choi's theorem, easy direction: the Choi matrix of a completely positive map is
positive semidefinite. -/
lemma choi_posSemidef [Fintype A] [DecidableEq A] [Fintype B]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} (hCP : IsCompletelyPositive Φ) :
    (choi Φ).PosSemidef := by
  classical
  set n := Fintype.card A with hn
  set ε : Fin n ≃ A := (Fintype.equivFin A).symm with hε
  set w : Fin n × A → ℂ := fun p => if ε p.1 = p.2 then 1 else 0 with hw
  set Ω : Matrix (Fin n × A) (Fin n × A) ℂ :=
      (replicateCol Unit w) * (replicateCol Unit w)ᴴ with hΩ
  have hΩpsd : Ω.PosSemidef := posSemidef_self_mul_conjTranspose _
  have hampl := hCP n Ω hΩpsd
  have hEq : choi Φ = (ampliate Φ (Fin n) Ω).submatrix
      (fun p => (ε.symm p.1, p.2)) (fun p => (ε.symm p.1, p.2)) := by
    ext p q
    have key : (fun (i j : A) => Ω (ε.symm p.1, i) (ε.symm q.1, j)) = single p.1 q.1 (1 : ℂ) := by
      funext i j
      simp only [hΩ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply,
        Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, hw,
        Matrix.single_apply, Equiv.apply_symm_apply]
      by_cases h1 : p.1 = i <;> by_cases h2 : q.1 = j <;> simp [h1, h2]
    simp only [Matrix.submatrix_apply, ampliate, choi, key]
  rw [hEq]
  exact hampl.submatrix _

set_option linter.deprecated false in
/-- Kraus decomposition: a completely positive map is a sum of conjugations
`ρ ↦ ∑ s, K s * ρ * (K s)ᴴ`. -/
lemma exists_kraus [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} (hCP : IsCompletelyPositive Φ) :
    ∃ K : (A × B) → Matrix B A ℂ, ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ := by
  classical
  obtain ⟨M, hM⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp (choi_posSemidef hCP)
  refine ⟨fun s => Matrix.of fun a i => star (M s (i, a)), ?_⟩
  intro ρ
  have hchoi : ∀ (i j : A) (a b : B),
      choi Φ (i, a) (j, b) = ∑ s, star (M s (i, a)) * M s (j, b) := by
    intro i j a b
    rw [hM]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hsingle : ∀ (i j : A) (a b : B),
      (Φ (single i j (ρ i j))) a b = ρ i j * choi Φ (i, a) (j, b) := by
    intro i j a b
    have h1 : single i j (ρ i j) = ρ i j • single i j (1 : ℂ) := by
      ext x y; simp [Matrix.single_apply]
    rw [h1, map_smul]
    simp [choi]
  ext a b
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  rw [map_sum]
  simp only [Matrix.sum_apply, map_sum, hsingle, hchoi]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_star,
    Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm₃ (fun i j s => ρ i j * (star (M s (i, a)) * M s (j, b)))]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The Kraus operators of a trace-preserving map satisfy the completeness relation. -/
lemma kraus_sum_eq_one [Fintype A] [DecidableEq A] [Fintype B] {R : Type*} [Fintype R]
    {Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ} {K : R → Matrix B A ℂ}
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ) (hTP : IsTracePreserving Φ) :
    ∑ s, (K s)ᴴ * K s = 1 := by
  classical
  ext i j
  have h := hTP (single j i 1)
  rw [hK] at h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.sum_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ite_and] at h ⊢
  rw [← h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Any isometry extends to a unitary between spaces of equal dimension: if the columns
of `W` are orthonormal and `f` embeds the column index type into `Z` with
`card Z = card Y`, then `W` consists of columns of a unitary matrix. -/
lemma exists_unitary_extension {X Y Z : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (W : Matrix Y X ℂ) (hW : Wᴴ * W = 1) {f : X → Z} (hf : Function.Injective f)
    (hcard : Fintype.card Z = Fintype.card Y) :
    ∃ U : Matrix Y Z ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ ∀ (y : Y) (x : X), U y (f x) = W y x := by
  classical
  set col : X → EuclideanSpace ℂ Y := fun x => WithLp.toLp 2 (fun y => W y x) with hcol
  set v : Z → EuclideanSpace ℂ Y := Function.extend f col 0 with hv
  have hinner : ∀ x x' : X, (inner ℂ (col x) (col x') : ℂ) = if x = x' then 1 else 0 := by
    intro x x'
    have h1 : (inner ℂ (col x) (col x') : ℂ) = ∑ y, star (W y x) * W y x' := by
      simp [hcol, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have h2 := congrFun (congrFun hW x) x'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h2
    rw [h1, ← h2]
  have horth : Orthonormal ℂ (Set.restrict (Set.range f) v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨z, x, rfl⟩ ⟨z', x', rfl⟩
    simp only [Set.restrict_apply, hv, hf.extend_apply]
    rw [hinner]
    simp [hf.eq_iff, Subtype.ext_iff]
  have hrank : Module.finrank ℂ (EuclideanSpace ℂ Y) = Fintype.card Z := by
    simp [hcard]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hrank
  have hbo := orthonormal_iff_ite.mp b.orthonormal
  set U : Matrix Y Z ℂ := Matrix.of (fun y z => (b z).ofLp y) with hU
  have h1 : Uᴴ * U = 1 := by
    ext z z'
    have hz := hbo z z'
    rw [PiLp.inner_apply] at hz
    simp only [hU, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.inner_apply] at hz ⊢
    rw [← hz]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : U * Uᴴ = 1 := by
    obtain ⟨g⟩ : Nonempty (Y ≃ Z) := ⟨Fintype.equivOfCardEq hcard.symm⟩
    have hV : (U.submatrix (Equiv.refl Y) g)ᴴ * (U.submatrix (Equiv.refl Y) g) = 1 := by
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h1,
        Matrix.submatrix_one_equiv]
    have hV2 := mul_eq_one_comm.mp hV
    ext y y'
    have hyy := congrFun (congrFun hV2 y) y'
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
      Equiv.refl_apply, Matrix.one_apply] at hyy ⊢
    rw [← hyy, ← Equiv.sum_comp g (fun z => U y z * star (U y' z))]
  refine ⟨U, h1, h2, ?_⟩
  intro y x
  have hbf := hb (f x) ⟨x, rfl⟩
  simp only [hU, Matrix.of_apply, hbf, hv, hf.extend_apply, hcol]

/-- Auxiliary form of the Stinespring dilation theorem: a map given by a Kraus
decomposition whose Kraus operators satisfy the completeness relation is a
unitary dilation. -/
private lemma stinespring_of_kraus [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R] (K : R → Matrix B A ℂ)
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hK : ∀ ρ : Matrix A A ℂ, Φ ρ = ∑ s, K s * ρ * (K s)ᴴ)
    (hT : ∑ s, (K s)ᴴ * K s = 1) :
    ∃ (dA dB : ℕ) (e : Fin dA) (U : Matrix (B × Fin dB) (A × Fin dA) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ ρ : Matrix A A ℂ, Φ ρ = ptrace (U * (ρ ⊗ₖ single e e 1) * Uᴴ) := by
  classical
  set a₀ : A := Classical.arbitrary A with ha₀
  set dB := Fintype.card (R × A) with hdB
  set dA := Fintype.card (B × R) with hdA
  set εB : Fin dB ≃ R × A := (Fintype.equivFin (R × A)).symm with hεB
  set εA : Fin dA ≃ B × R := (Fintype.equivFin (B × R)).symm with hεA
  set e : Fin dA := εA.symm (Classical.arbitrary B, Classical.arbitrary R) with he
  set W : Matrix (B × Fin dB) A ℂ :=
    Matrix.of (fun p i => K (εB p.2).1 p.1 i * (if (εB p.2).2 = a₀ then 1 else 0)) with hWdef
  have hW : Wᴴ * W = 1 := by
    ext i j
    have h := congrFun (congrFun hT i) j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type, ← h]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hfg : ∀ t : Fin dB, Wᴴ i (b, t) * W (b, t) j =
        star (K (εB t).1 b i) * K (εB t).1 b j * (if (εB t).2 = a₀ then (1 : ℂ) else 0) := by
      intro t
      simp only [hWdef, Matrix.conjTranspose_apply, Matrix.of_apply]
      split_ifs <;> simp
    refine (Fintype.sum_equiv εB (fun t : Fin dB => Wᴴ i (b, t) * W (b, t) j)
      (fun r : R × A => star (K r.1 b i) * K r.1 b j * (if r.2 = a₀ then (1 : ℂ) else 0))
      hfg).trans ?_
    rw [Fintype.sum_prod_type]
    simp
  have hf : Function.Injective (fun i : A => (i, e)) := by
    intro x y h; simpa using h
  have hcard : Fintype.card (A × Fin dA) = Fintype.card (B × Fin dB) := by
    simp only [Fintype.card_prod, Fintype.card_fin, hdA, hdB]
    ring
  obtain ⟨U, hU1, hU2, hUW⟩ := exists_unitary_extension W hW hf hcard
  refine ⟨dA, dB, e, U, hU1, hU2, ?_⟩
  intro ρ
  have hconj : U * (ρ ⊗ₖ single e e 1) * Uᴴ = W * ρ * Wᴴ := by
    ext y y'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.single_apply, mul_ite, mul_zero,
      ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one, hUW]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e) ?_]
    · simp [hUW]
    · intro u _ hu
      simp [Ne.symm hu]
  rw [hconj, hK ρ]
  ext b b'
  simp only [ptrace, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hFG : ∀ t : Fin dB,
      (∑ j, (∑ i, W (b, t) i * ρ i j) * star (W (b', t) j)) =
        (if (εB t).2 = a₀ then (1 : ℂ) else 0) *
          ∑ j, (∑ i, K (εB t).1 b i * ρ i j) * star (K (εB t).1 b' j) := by
    intro t
    simp only [hWdef, Matrix.of_apply]
    split_ifs with h <;> simp [Finset.mul_sum, Finset.sum_mul]
  symm
  refine (Fintype.sum_equiv εB
    (fun t : Fin dB => ∑ j, (∑ i, W (b, t) i * ρ i j) * star (W (b', t) j))
    (fun r : R × A => (if r.2 = a₀ then (1 : ℂ) else 0) *
      ∑ j, (∑ i, K r.1 b i * ρ i j) * star (K r.1 b' j)) hFG).trans ?_
  rw [Fintype.sum_prod_type]
  simp

/-- **Stinespring dilation.** Every completely positive trace-preserving map
`Φ : Matrix A A ℂ → Matrix B B ℂ` is the compression of a unitary conjugation:
there are ancilla spaces `ℂ^dA`, `ℂ^dB`, a pure ancilla state `|e⟩⟨e|` and a unitary
`U : ℂ^A ⊗ ℂ^dA → ℂ^B ⊗ ℂ^dB` such that
`Φ ρ = Tr_{ℂ^dB} (U (ρ ⊗ |e⟩⟨e|) U†)` for every `ρ`. -/
theorem stinespring [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (Φ : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : IsCompletelyPositive Φ) (hTP : IsTracePreserving Φ) :
    ∃ (dA dB : ℕ) (e : Fin dA) (U : Matrix (B × Fin dB) (A × Fin dA) ℂ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      ∀ ρ : Matrix A A ℂ, Φ ρ = ptrace (U * (ρ ⊗ₖ single e e 1) * Uᴴ) := by
  classical
  obtain ⟨K, hK⟩ := exists_kraus hCP
  exact stinespring_of_kraus K Φ hK (kraus_sum_eq_one hK hTP)

/-- The identity channel is completely positive. -/
lemma id_isCompletelyPositive [Fintype A] [DecidableEq A] :
    IsCompletelyPositive (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := by
  intro k ρ hρ
  have h : ampliate (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) (Fin k) ρ = ρ := by
    ext p q; rfl
  rw [h]
  exact hρ

/-- The identity channel is trace preserving. -/
lemma id_isTracePreserving [Fintype A] :
    IsTracePreserving (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := fun _ => rfl

end QI

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

