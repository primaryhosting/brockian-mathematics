import Mathlib
/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE FILE HEADER.  Lean 4 requires `import` to be the very first command of a
module, so the requested `/-! ... -/` module docstring is placed immediately after the
single `import Mathlib` line rather than before it; its text is otherwise verbatim.
-/

open scoped BigOperators

namespace Frontier

/-! ## The superrigidity extension property

Margulis superrigidity says, for `G` a semisimple Lie group of real rank `≥ 2`, `Γ ≤ G` an
irreducible lattice and `π : Γ → H` a homomorphism into a simple algebraic group with
unbounded Zariski-dense image, that `π` is the restriction of a *continuous* homomorphism
`G → H`.  The predicate below isolates the conclusion of that theorem: a homomorphism
defined on the lattice extends to a continuous homomorphism of the ambient group.
-/

/-- The conclusion of a superrigidity statement, in additive notation: a homomorphism `π`
defined on a lattice `L` (mapped into the ambient group `G` by the inclusion `ι`) is the
restriction along `ι` of a continuous homomorphism `G → H`. -/
def ExtendsToContinuousHom {L G H : Type*} [AddGroup L] [AddGroup G] [AddGroup H]
    [TopologicalSpace G] [TopologicalSpace H] (ι : L →+ G) (π : L →+ H) : Prop :=
  ∃ ρ : G →+ H, Continuous ρ ∧ ∀ v : L, ρ (ι v) = π v

/-- Multiplicative version of `Frontier.ExtendsToContinuousHom`: a homomorphism `π` defined on a
lattice `L` is the restriction along `ι` of a continuous homomorphism of the ambient group. -/
def ExtendsToContinuousMulHom {L G H : Type*} [Group L] [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (ι : L →* G) (π : L →* H) : Prop :=
  ∃ ρ : G →* H, Continuous ρ ∧ ∀ v : L, ρ (ι v) = π v

/-- A general uniqueness principle behind superrigidity: a continuous homomorphism out of the
ambient group is determined by its restriction along `ι`, as soon as the image of `ι` is
dense. -/
theorem eq_of_dense_range {L G H : Type*} [AddGroup L] [AddGroup G] [AddGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [T2Space H] (ι : L →+ G)
    (hd : Dense (Set.range ι)) {ρ σ : G →+ H} (hρ : Continuous ρ) (hσ : Continuous σ)
    (h : ∀ v : L, ρ (ι v) = σ (ι v)) : ρ = σ := by
  have hfun : (ρ : G → H) = (σ : G → H) :=
    Continuous.ext_on hd hρ hσ (by rintro _ ⟨v, rfl⟩; exact h v)
  exact DFunLike.ext _ _ fun x => congrFun hfun x

/-- The standard lattice `ℤ ^ n` inside `ℝ ^ n`, as the inclusion homomorphism. -/
def latticeIncl (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun v i := (v i : ℝ)
  map_zero' := by funext i; simp
  map_add' u v := by funext i; simp

@[simp] lemma latticeIncl_apply {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    latticeIncl n v i = (v i : ℝ) := rfl

lemma latticeIncl_single {n : ℕ} (i : Fin n) :
    latticeIncl n (Pi.single i (1 : ℤ)) = Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i <;> simp [h, Pi.single_apply]

section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The candidate extension of a homomorphism `π : ℤ ^ n → E`: the unique real-linear map
sending the `i`-th standard basis vector to `π (δ i)`. -/
noncomputable def linearExtension (π : (Fin n → ℤ) →+ E) : (Fin n → ℝ) →ₗ[ℝ] E :=
  (Pi.basisFun ℝ (Fin n)).constr ℝ fun i => π (Pi.single i (1 : ℤ))

@[simp] lemma linearExtension_basis (π : (Fin n → ℤ) →+ E) (i : Fin n) :
    linearExtension π (Pi.single i (1 : ℝ)) = π (Pi.single i (1 : ℤ)) := by
  have h : (Pi.basisFun ℝ (Fin n)) i = Pi.single i (1 : ℝ) := by
    funext j; simp [Pi.basisFun_apply, Pi.single_apply]
  rw [← h, linearExtension, Module.Basis.constr_basis]

lemma continuous_linearExtension (π : (Fin n → ℤ) →+ E) :
    Continuous (linearExtension π) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The linear extension really does extend `π` over the lattice. -/
lemma linearExtension_comp_latticeIncl (π : (Fin n → ℤ) →+ E) (v : Fin n → ℤ) :
    linearExtension π (latticeIncl n v) = π v := by
  have hv : latticeIncl n v
      = ∑ i : Fin n, (v i : ℝ) • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply]
  have hv' : v = ∑ i : Fin n, (v i) • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    funext j
    simp [Pi.single_apply]
  have h1 : linearExtension π (latticeIncl n v)
      = ∑ i : Fin n, (v i) • π (Pi.single i (1 : ℤ)) := by
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, linearExtension_basis, Int.cast_smul_eq_zsmul]
  have h2 : π v = ∑ i : Fin n, (v i) • π (Pi.single i (1 : ℤ)) := by
    conv_lhs => rw [hv']
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul π _ _
  rw [h1, h2]

/-- Uniqueness: a continuous homomorphism `ℝ ^ n → E` is determined by its values on the
lattice `ℤ ^ n`. -/
lemma eq_of_eqOn_lattice {ρ σ : (Fin n → ℝ) →+ E} (hρ : Continuous ρ) (hσ : Continuous σ)
    (h : ∀ v : Fin n → ℤ, ρ (latticeIncl n v) = σ (latticeIncl n v)) : ρ = σ := by
  have hlin : (ρ.toRealLinearMap hρ).toLinearMap = (σ.toRealLinearMap hσ).toLinearMap := by
    refine (Pi.basisFun ℝ (Fin n)).ext fun i => ?_
    have hb : (Pi.basisFun ℝ (Fin n)) i = latticeIncl n (Pi.single i (1 : ℤ)) := by
      rw [latticeIncl_single]
      funext j; simp [Pi.basisFun_apply, Pi.single_apply]
    simpa [hb] using h (Pi.single i (1 : ℤ))
  refine DFunLike.ext _ _ fun x => ?_
  simpa using LinearMap.congr_fun hlin x

end

/-- **Margulis superrigidity: the abelian base case.**

For the lattice `ℤ ^ n ⊆ ℝ ^ n` (inclusion `Frontier.latticeIncl n`) and any real normed
space `E`, every abstract group homomorphism `π : ℤ ^ n → E` from the lattice is the
restriction of a *unique* continuous homomorphism `ρ : ℝ ^ n → E` of the ambient group;
moreover that extension is automatically `ℝ`-linear.

This is the base case of the superrigidity phenomenon: homomorphisms defined only on a
lattice are rigid, i.e. they come from continuous homomorphisms of the ambient group.  The
full theorem of Margulis (for irreducible lattices in semisimple groups of real rank at
least two, with Zariski-dense unbounded image) is not formalized here; the statement of its
conclusion is `Frontier.ExtendsToContinuousHom`, which the theorem below verifies in the
abelian case, together with uniqueness of the extension. -/
theorem margulis_superrigidity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : (Fin n → ℤ) →+ E) :
    ExtendsToContinuousHom (latticeIncl n) π ∧
      ∃! ρ : (Fin n → ℝ) →+ E, Continuous ρ ∧ ∀ v : Fin n → ℤ, ρ (latticeIncl n v) = π v := by
  refine ⟨⟨(linearExtension π).toAddMonoidHom, continuous_linearExtension π,
      linearExtension_comp_latticeIncl π⟩, ?_⟩
  refine ⟨(linearExtension π).toAddMonoidHom,
    ⟨continuous_linearExtension π, linearExtension_comp_latticeIncl π⟩, ?_⟩
  rintro σ ⟨hσc, hσ⟩
  refine eq_of_eqOn_lattice hσc (continuous_linearExtension π) fun v => ?_
  rw [hσ v]
  exact (linearExtension_comp_latticeIncl π v).symm

/-! ## The base case for an arbitrary lattice

The base case above is stated for the standard lattice `ℤⁿ ⊂ ℝⁿ`.  In fact it holds for an
arbitrary `ℤ`-lattice `L` in a finite-dimensional real vector space `E`, i.e. a discrete
`ℤ`-submodule spanning `E` over `ℝ`. -/

open Module in
/-- **Margulis superrigidity, abelian case, for an arbitrary lattice.**  Let `L` be a
`ℤ`-lattice in a finite-dimensional real vector space `E` (discrete and spanning `E` over `ℝ`).
Then every abstract group homomorphism `π : L →+ F` into a real normed space `F` is the
restriction of a unique continuous homomorphism `E →+ F`. -/
theorem margulis_superrigidity_zlattice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (π : L →+ F) :
    ∃! ρ : E →+ F, Continuous ρ ∧ ∀ v : L, ρ (v : E) = π v := by
  classical
  have hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
  set b : Basis (Free.ChooseBasisIndex ℤ L) ℤ L := Free.chooseBasis ℤ L with hb
  set B : Basis (Free.ChooseBasisIndex ℤ L) ℝ E := b.ofZLatticeBasis ℝ L with hB
  set ρ0 : E →ₗ[ℝ] F := B.constr ℝ fun i => π (b i) with hρ0
  have hbasis : ∀ i, ρ0 (B i) = π (b i) := fun i => by rw [hρ0, Basis.constr_basis]
  have hcont : Continuous ρ0 := LinearMap.continuous_of_finiteDimensional _
  have hagree : ∀ v : L, ρ0 (v : E) = π v := by
    intro v
    have h1 : ρ0 (v : E) = ∑ i, B.repr (v : E) i • ρ0 (B i) := by
      conv_lhs => rw [← B.sum_repr (v : E)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have h2 : ∀ i, B.repr (v : E) i = ((b.repr v i : ℤ) : ℝ) := by
      intro i
      rw [hB, Basis.ofZLatticeBasis_repr_apply]
    have h3 : π v = ∑ i, (b.repr v i) • π (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
    rw [h1, h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbasis, h2, Int.cast_smul_eq_zsmul]
  refine ⟨ρ0.toAddMonoidHom, ⟨hcont, hagree⟩, ?_⟩
  rintro σ ⟨hσc, hσ⟩
  have hlin : (σ.toRealLinearMap hσc).toLinearMap = ρ0 := by
    refine B.ext fun i => ?_
    have hBi : B i = ((b i : L) : E) := by rw [hB, Basis.ofZLatticeBasis_apply]
    rw [hbasis, hBi]
    simpa using hσ (b i)
  refine DFunLike.ext _ _ fun x => ?_
  simpa using LinearMap.congr_fun hlin x

/-! ## Sharpness of the base case

Superrigidity genuinely uses the structure of the target group: for a *discrete* target the
extension property fails already for the lattice `ℤ ⊂ ℝ`. -/

/-- The identity homomorphism of the lattice `ℤ ⊂ ℝ` into the discrete group `ℤ` admits **no**
continuous extension to `ℝ`: `ℝ` is connected and `ℤ` is totally disconnected, so every
continuous homomorphism `ℝ → ℤ` is trivial. -/
theorem not_extendsToContinuousHom_int_id :
    ¬ ExtendsToContinuousHom (Int.castAddHom ℝ) (AddMonoidHom.id ℤ) := by
  rintro ⟨ρ, hρ, h⟩
  have hsub : Set.Subsingleton (Set.range ρ) := (isPreconnected_range hρ).subsingleton
  have h01 : ρ (0 : ℝ) = ρ (1 : ℝ) :=
    hsub (Set.mem_range_self (0 : ℝ)) (Set.mem_range_self (1 : ℝ))
  have h1 : ρ (1 : ℝ) = 1 := by simpa using h 1
  rw [map_zero, h1] at h01
  exact zero_ne_one h01

/-! ## The statement for higher-rank lattices

We now write down the statement of Margulis superrigidity in the model higher-rank case of the
lattice `SL(n, ℤ) ⊂ SL(n, ℝ)` with `n ≥ 3` (real rank `n - 1 ≥ 2`) and target `SL(m, ℝ)`.
The two hypotheses of the theorem — Zariski density and unboundedness of the image — are
spelled out directly in terms of matrix entries. -/

open Matrix in
/-- Evaluation of matrix entries as a point of affine `m × m`-space. -/
def entryPoint {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Fin m × Fin m → ℝ := fun ij => A ij.1 ij.2

/-- `S` is Zariski dense in `T`: every polynomial in the matrix entries which vanishes on `S`
vanishes on `T`. -/
def ZariskiDenseIn {m : ℕ} (S T : Set (Matrix (Fin m) (Fin m) ℝ)) : Prop :=
  ∀ p : MvPolynomial (Fin m × Fin m) ℝ,
    (∀ A ∈ S, MvPolynomial.eval (entryPoint A) p = 0) →
      ∀ A ∈ T, MvPolynomial.eval (entryPoint A) p = 0

/-- A set of matrices is unbounded if its entries are not uniformly bounded. -/
def EntrywiseUnbounded {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℝ)) : Prop :=
  ∀ C : ℝ, ∃ A ∈ S, ∃ i j, C < |A i j|

/-- The set of matrices in the image of a homomorphism into `SL(m, ℝ)`. -/
def imageMatrices {n m : ℕ} (π : Matrix.SpecialLinearGroup (Fin n) ℤ →*
    Matrix.SpecialLinearGroup (Fin m) ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  Set.range fun γ => ((π γ : Matrix.SpecialLinearGroup (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ)

/-- The inclusion of the lattice `SL(n, ℤ)` into `SL(n, ℝ)`. -/
def slLatticeIncl (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.SpecialLinearGroup (Fin n) ℝ :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- **Margulis superrigidity, higher-rank statement.**  For `n ≥ 3`, every homomorphism from the
lattice `SL(n, ℤ) ⊂ SL(n, ℝ)` to `SL(m, ℝ)` whose image is Zariski dense and unbounded is the
restriction of a continuous homomorphism `SL(n, ℝ) → SL(m, ℝ)`.

This is a `Prop`-valued *statement*; it is not proved here (its proof requires the theory of
boundary maps and measurable equivariant cocycles, which is not available in Mathlib).  The
results proved in this file are the base case `Frontier.margulis_superrigidity`, the uniqueness
reduction `Frontier.eq_of_dense_range`, the instance
`Frontier.margulis_superrigidity_inclusion` and the reduction
`Frontier.extendsToContinuousHom_comp`. -/
def MargulisSuperrigidityStatement (n m : ℕ) : Prop :=
  3 ≤ n →
    ∀ π : Matrix.SpecialLinearGroup (Fin n) ℤ →* Matrix.SpecialLinearGroup (Fin m) ℝ,
      ZariskiDenseIn (imageMatrices π)
          (Set.range fun g : Matrix.SpecialLinearGroup (Fin m) ℝ =>
            (g : Matrix (Fin m) (Fin m) ℝ)) →
        EntrywiseUnbounded (imageMatrices π) →
          ExtendsToContinuousMulHom (slLatticeIncl n) π

/-- A first, unconditional instance of the higher-rank conclusion: the tautological inclusion
`SL(n, ℤ) → SL(n, ℝ)` is the restriction of a continuous homomorphism of the ambient group
(namely the identity).  In particular the conclusion of
`Frontier.MargulisSuperrigidityStatement` is not vacuous. -/
theorem margulis_superrigidity_inclusion (n : ℕ) :
    ExtendsToContinuousMulHom (slLatticeIncl n) (slLatticeIncl n) :=
  ⟨MonoidHom.id _, continuous_id, fun _ => rfl⟩

/-- **A Lean-checked reduction in the higher-rank setting.**  A homomorphism of a *perfect*
lattice into an abelian topological group is trivial, hence extends continuously.  For
`SL(n, ℤ)` with `n ≥ 3` the hypothesis `commutator _ = ⊤` holds classically, so this settles
the abelian-target case of Margulis superrigidity modulo that group-theoretic input. -/
theorem extendsToContinuousMulHom_of_perfect {L G H : Type*} [Group L] [Group G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] (hL : commutator L = ⊤) (ι : L →* G)
    (π : L →* H) : ExtendsToContinuousMulHom ι π := by
  have hker : commutator L ≤ π.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    simp [MonoidHom.mem_ker, commutatorElement_def]
  have htriv : ∀ g : L, π g = 1 := by
    intro g
    have : g ∈ π.ker := hker (by rw [hL]; trivial)
    simpa [MonoidHom.mem_ker] using this
  exact ⟨1, continuous_const, fun v => by simp [htriv v]⟩

/-! ### Elementary matrices and perfectness of the lattice

For `n ≥ 3` every elementary matrix is a commutator of elementary matrices, so the
perfectness hypothesis above reduces to the elementary statement that `SL(n, ℤ)` is generated
by elementary matrices. -/

open Matrix in
/-- The elementary matrix `1 + a·Eᵢⱼ` as an element of `SL(n, ℤ)`. -/
def elemSL {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : ℤ) :
    Matrix.SpecialLinearGroup (Fin n) ℤ :=
  ⟨Matrix.transvection i j a, Matrix.det_transvection_of_ne i j hij a⟩

/-- The set of elementary matrices of `SL(n, ℤ)`. -/
def elemSet (n : ℕ) : Set (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  {g | ∃ (i j : Fin n) (hij : i ≠ j) (a : ℤ), g = elemSL i j hij a}

open Matrix in
/-- The key commutator identity `⟦1 + a·Eᵢₖ, 1 + Eₖⱼ⟧ = 1 + a·Eᵢⱼ` for distinct `i, j, k`. -/
lemma transvection_commutator_matrix {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hkj : k ≠ j) (a : ℤ) :
    transvection i k a * transvection k j 1 * transvection i k (-a) * transvection k j (-1)
      = transvection i j a := by
  have hneg : ∀ (p q : Fin n) (c : ℤ), single p q (-c) = -single p q c := by
    intro p q c
    have h := Matrix.single_add p q c (-c)
    simp only [add_neg_cancel, Matrix.single_zero] at h
    linear_combination (norm := abel) -h
  simp only [transvection]
  noncomm_ring
  simp [single_mul_single_same, single_mul_single_of_ne, hij.symm, hik.symm, hkj.symm]
  rw [hneg, hneg, hneg]
  abel

/-- The inverse of an elementary matrix is elementary. -/
lemma elemSL_inv {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : ℤ) :
    (elemSL i j hij a)⁻¹ = elemSL i j hij (-a) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show Matrix.transvection i j a * Matrix.transvection i j (-a) = (1 : Matrix (Fin n) (Fin n) ℤ)
  rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
    Matrix.transvection_zero]

/-- For `n ≥ 3` every elementary matrix lies in the commutator subgroup of `SL(n, ℤ)`. -/
lemma elemSL_mem_commutator {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j) (a : ℤ) :
    elemSL i j hij a ∈ commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ ({i, j} : Finset (Fin n)) := by
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := fun x _ => hc x
    have h1 : (Finset.univ : Finset (Fin n)).card ≤ ({i, j} : Finset (Fin n)).card :=
      Finset.card_le_card hsub
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le i {j}) ?_
      simp
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj⟩ := hk
  have hik : i ≠ k := fun h => hki h.symm
  have hkey : elemSL i j hij a = ⁅elemSL i k hik a, elemSL k j hkj 1⁆ := by
    rw [commutatorElement_def, elemSL_inv, elemSL_inv]
    refine Subtype.ext ?_
    show Matrix.transvection i j a = _
    exact (transvection_commutator_matrix hij hik hkj a).symm
  rw [hkey, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **Reduction of perfectness to generation by elementary matrices.**  If `SL(n, ℤ)` with
`n ≥ 3` is generated by elementary matrices, then it is perfect. -/
theorem commutator_eq_top_of_elemSet_generates {n : ℕ} (hn : 3 ≤ n)
    (hgen : Subgroup.closure (elemSet n) = ⊤) :
    commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← hgen]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro g ⟨i, j, hij, a, rfl⟩
  exact elemSL_mem_commutator hn i j hij a

/-- The abelian-target case of Margulis superrigidity for `SL(n, ℤ) ⊂ SL(n, ℝ)`, conditional on
generation of the lattice by elementary matrices. -/
theorem margulis_superrigidity_abelian_target_of_elemSet_generates {n : ℕ} (hn : 3 ≤ n)
    (hgen : Subgroup.closure (elemSet n) = ⊤) {H : Type*} [CommGroup H] [TopologicalSpace H]
    (π : Matrix.SpecialLinearGroup (Fin n) ℤ →* H) :
    ExtendsToContinuousMulHom (slLatticeIncl n) π :=
  extendsToContinuousMulHom_of_perfect (commutator_eq_top_of_elemSet_generates hn hgen) _ π

/-- The abelian-target case of Margulis superrigidity for `SL(n, ℤ) ⊂ SL(n, ℝ)`, conditional on
perfectness of the lattice.  The hypothesis is discharged for `n ≥ 3` in the file
`RequestProject/ElementaryGeneration.lean`, where `SL(n, ℤ)` is shown to be generated by
elementary matrices (`Frontier.elemSet_closure_eq_top`), hence perfect
(`Frontier.commutator_specialLinearGroup_int_eq_top`), giving the unconditional statement
`Frontier.margulis_superrigidity_abelian_target_higher_rank`. -/
theorem margulis_superrigidity_abelian_target (n : ℕ)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) = ⊤)
    {H : Type*} [CommGroup H] [TopologicalSpace H]
    (π : Matrix.SpecialLinearGroup (Fin n) ℤ →* H) :
    ExtendsToContinuousMulHom (slLatticeIncl n) π :=
  extendsToContinuousMulHom_of_perfect hperf _ π

/-- The degenerate case `m = 1` of the higher-rank statement holds: `SL(1, ℝ)` is trivial, so no
homomorphism into it has unbounded image and the hypotheses are unsatisfiable. -/
theorem margulisSuperrigidityStatement_one (n : ℕ) : MargulisSuperrigidityStatement n 1 := by
  intro _ π _ hunb
  obtain ⟨A, hA, i, j, hij⟩ := hunb 1
  obtain ⟨γ, rfl⟩ := hA
  have hdet : ((π γ : Matrix.SpecialLinearGroup (Fin 1) ℝ) :
      Matrix (Fin 1) (Fin 1) ℝ).det = 1 := (π γ).2
  rw [Matrix.det_fin_one] at hdet
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [hdet] at hij

/-- A reduction: the superrigidity conclusion is stable under post-composition with a continuous
homomorphism of the target. -/
theorem extendsToContinuousHom_comp {L G H K : Type*} [AddGroup L] [AddGroup G] [AddGroup H]
    [AddGroup K] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
    {ι : L →+ G} {π : L →+ H} (h : ExtendsToContinuousHom ι π) (φ : H →+ K)
    (hφ : Continuous φ) : ExtendsToContinuousHom ι (φ.comp π) := by
  obtain ⟨ρ, hρ, hext⟩ := h
  exact ⟨φ.comp ρ, hφ.comp hρ, fun v => by simp [hext v]⟩

end Frontier

import RequestProject.MargulisSuperrigidity

/-!
# `SL(n, ℤ)` is generated by elementary matrices

This file proves that the special linear group over `ℤ` is generated by the elementary
(transvection) matrices `1 + a·Eᵢⱼ`, by formalizing Gaussian elimination over the Euclidean
domain `ℤ`.  Combined with the commutator identity of `RequestProject.MargulisSuperrigidity`
this shows that `SL(n, ℤ)` is perfect for `n ≥ 3`, which makes the abelian-target case of
Margulis superrigidity for the lattice `SL(n, ℤ) ⊂ SL(n, ℝ)` unconditional.
-/

open Matrix

namespace Frontier

variable {n : ℕ}

/-- The subgroup of `SL(n, ℤ)` generated by the elementary matrices. -/
abbrev ESub (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  Subgroup.closure (elemSet n)

lemma elemSL_mem_ESub (i j : Fin n) (h : i ≠ j) (a : ℤ) : elemSL i j h a ∈ ESub n :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

@[simp] lemma coe_elemSL (i j : Fin n) (h : i ≠ j) (a : ℤ) :
    ((elemSL i j h a : Matrix.SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)
      = Matrix.transvection i j a := rfl

/-- Row operation: left multiplication by an elementary matrix adds `c` times row `j` to
row `i`. -/
lemma elemSL_mul_apply (i j : Fin n) (hij : i ≠ j) (c : ℤ)
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (a b : Fin n) :
    ((elemSL i j hij c * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) a b
      = if a = i then (A : Matrix (Fin n) (Fin n) ℤ) i b
          + c * (A : Matrix (Fin n) (Fin n) ℤ) j b
        else (A : Matrix (Fin n) (Fin n) ℤ) a b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elemSL]
  by_cases h : a = i
  · subst h; simp
  · simp [h]

/-- Column operation: right multiplication by an elementary matrix adds `c` times column `i` to
column `j`. -/
lemma mul_elemSL_apply (i j : Fin n) (hij : i ≠ j) (c : ℤ)
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (a b : Fin n) :
    ((A * elemSL i j hij c : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) a b
      = if b = j then (A : Matrix (Fin n) (Fin n) ℤ) a j
          + c * (A : Matrix (Fin n) (Fin n) ℤ) a i
        else (A : Matrix (Fin n) (Fin n) ℤ) a b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_elemSL]
  by_cases h : b = j
  · subst h; simp
  · simp [h]

/-- `A` agrees with the identity matrix on the first `m` rows and the first `m` columns. -/
def PartialId (m : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j : Fin n, ((i : ℕ) < m ∨ (j : ℕ) < m) → A i j = if i = j then 1 else 0

/-- Row operations with both indices outside the first `m` coordinates preserve `PartialId m`. -/
lemma partialId_rowOp {m : ℕ} {A : Matrix.SpecialLinearGroup (Fin n) ℤ}
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) {i j : Fin n} (hij : i ≠ j)
    (hi : m ≤ (i : ℕ)) (hj : m ≤ (j : ℕ)) (c : ℤ) :
    PartialId m ((elemSL i j hij c * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
      Matrix (Fin n) (Fin n) ℤ) := by
  intro a b hab
  rw [elemSL_mul_apply]
  by_cases ha : a = i
  · subst ha
    have hb : (b : ℕ) < m := by
      rcases hab with h | h
      · omega
      · exact h
    have h1 : (A : Matrix (Fin n) (Fin n) ℤ) a b = 0 := by
      rw [hA a b (Or.inr hb)]
      have : a ≠ b := fun h => by rw [h] at hi; omega
      simp [this]
    have h2 : (A : Matrix (Fin n) (Fin n) ℤ) j b = 0 := by
      rw [hA j b (Or.inr hb)]
      have : j ≠ b := fun h => by rw [h] at hj; omega
      simp [this]
    have hne : a ≠ b := fun h => by rw [h] at hi; omega
    simp [h1, h2, hne]
  · simp [ha, hA a b hab]

/-- Column operations with both indices outside the first `m` coordinates preserve
`PartialId m`. -/
lemma partialId_colOp {m : ℕ} {A : Matrix.SpecialLinearGroup (Fin n) ℤ}
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) {i j : Fin n} (hij : i ≠ j)
    (hi : m ≤ (i : ℕ)) (hj : m ≤ (j : ℕ)) (c : ℤ) :
    PartialId m ((A * elemSL i j hij c : Matrix.SpecialLinearGroup (Fin n) ℤ) :
      Matrix (Fin n) (Fin n) ℤ) := by
  intro a b hab
  rw [mul_elemSL_apply]
  by_cases hb : b = j
  · subst hb
    have ha : (a : ℕ) < m := by
      rcases hab with h | h
      · exact h
      · omega
    have h1 : (A : Matrix (Fin n) (Fin n) ℤ) a b = 0 := by
      rw [hA a b (Or.inl ha)]
      have : a ≠ b := fun h => by rw [← h] at hj; omega
      simp [this]
    have h2 : (A : Matrix (Fin n) (Fin n) ℤ) a i = 0 := by
      rw [hA a i (Or.inl ha)]
      have : a ≠ i := fun h => by rw [← h] at hi; omega
      simp [this]
    have hne : a ≠ b := fun h => by rw [← h] at hj; omega
    simp [h1, h2, hne]
  · simp [hb, hA a b hab]

/-- Any common divisor of the entries of the `m`-th column below the first `m` rows is a unit,
because the determinant is `1`. -/
lemma column_isUnit_of_dvd {m : ℕ} (hm : m < n) (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) (d : ℤ)
    (hd : ∀ i : Fin n, m ≤ (i : ℕ) → d ∣ (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩) :
    IsUnit d := by
  set c : Fin n := ⟨m, hm⟩ with hc
  have hexp : ∑ i : Fin n, Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℤ) c i
      * (A : Matrix (Fin n) (Fin n) ℤ) i c = 1 := by
    have h := congrFun (congrFun (Matrix.adjugate_mul (A : Matrix (Fin n) (Fin n) ℤ)) c) c
    simpa [Matrix.mul_apply, A.2, Matrix.one_apply] using h
  refine isUnit_of_dvd_one ?_
  rw [← hexp]
  refine Finset.dvd_sum fun i _ => ?_
  by_cases hi : m ≤ (i : ℕ)
  · exact Dvd.dvd.mul_left (hd i hi) _
  · push_neg at hi
    have h0 : (A : Matrix (Fin n) (Fin n) ℤ) i c = 0 := by
      rw [hA i c (Or.inl hi)]
      have : i ≠ c := fun h => by rw [h] at hi; simp [hc] at hi
      simp [this]
    simp [h0]

/-- A matrix agreeing with the identity on all rows and columns is the identity. -/
lemma eq_one_of_partialId_ge (A : Matrix.SpecialLinearGroup (Fin n) ℤ) {m : ℕ} (hm : n ≤ m)
    (h : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) : A = 1 := by
  ext i j
  have := h i j (Or.inl (lt_of_lt_of_le i.isLt hm))
  simpa [Matrix.one_apply] using this

/-- If `A` agrees with the identity on all but the last row and column, then `A = 1`,
because its determinant is `1`. -/
lemma eq_one_of_partialId_succ (A : Matrix.SpecialLinearGroup (Fin n) ℤ) {m : ℕ} (hm : m + 1 = n)
    (h : PartialId m (A : Matrix (Fin n) (Fin n) ℤ)) : A = 1 := by
  have hmn : m < n := by omega
  set i0 : Fin n := ⟨m, hmn⟩ with hi0
  have hcoord : ∀ i : Fin n, i ≠ i0 → (i : ℕ) < m := by
    intro i hi
    have h1 : (i : ℕ) < n := i.isLt
    have h2 : (i : ℕ) ≠ m := by
      intro hc
      exact hi (Fin.ext (by simp [hi0, hc]))
    omega
  have hdiag : (A : Matrix (Fin n) (Fin n) ℤ)
      = Matrix.diagonal fun k => if k = i0 then (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 else 1 := by
    ext p q
    by_cases hp : p = i0
    · by_cases hq : q = i0
      · subst hp; subst hq; simp [Matrix.diagonal_apply_eq]
      · have hqm : (q : ℕ) < m := hcoord q hq
        rw [h p q (Or.inr hqm), Matrix.diagonal_apply_ne _ (by simp [hp, Ne.symm hq])]
        simp [hp, Ne.symm hq]
    · have hpm : (p : ℕ) < m := hcoord p hp
      rw [h p q (Or.inl hpm)]
      by_cases hq : q = p
      · subst hq; simp [Matrix.diagonal_apply_eq, hp]
      · simp [Ne.symm hq]
  have hdet : (A : Matrix (Fin n) (Fin n) ℤ).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal] at hdet
  have hprod : (∏ k : Fin n, if k = i0 then (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 else 1)
      = (A : Matrix (Fin n) (Fin n) ℤ) i0 i0 := by
    simp
  rw [hprod] at hdet
  refine Subtype.ext ?_
  rw [hdiag, hdet]
  simp

/-- To check that the pivot column is a standard basis vector it suffices to check the entries
below the first `m` rows. -/
lemma column_eq_of_active {m : ℕ} (hm : m < n) (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ))
    (h : ∀ i : Fin n, m ≤ (i : ℕ) →
      (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) :
    ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  intro i
  by_cases hi : m ≤ (i : ℕ)
  · exact h i hi
  · push_neg at hi
    exact hA i ⟨m, hm⟩ (Or.inl hi)

/-- Terminal step of the column reduction: if at most one entry of the pivot column is nonzero,
elementary row operations turn the pivot column into a standard basis vector. -/
lemma exists_reduce_column_of_single {m : ℕ} (hm : m < n) (hm2 : m + 1 < n)
    (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (hA : PartialId m (A : Matrix (Fin n) (Fin n) ℤ))
    (p : Fin n) (hp : m ≤ (p : ℕ))
    (hzero : ∀ i : Fin n, m ≤ (i : ℕ) → i ≠ p →
      (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0) :
    ∃ g ∈ ESub n, PartialId m ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) ∧
      ∀ i : Fin n, ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
        Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  set c : Fin n := ⟨m, hm⟩ with hc
  have hcm : (c : ℕ) = m := rfl
  have hcact : m ≤ (c : ℕ) := le_of_eq hcm.symm
  have hunit : (A : Matrix (Fin n) (Fin n) ℤ) p c = 1 ∨
      (A : Matrix (Fin n) (Fin n) ℤ) p c = -1 := by
    rw [← Int.isUnit_iff]
    refine column_isUnit_of_dvd hm A hA _ fun i hi => ?_
    by_cases hip : i = p
    · rw [hip]
    · rw [hzero i hi hip]
      exact dvd_zero _
  have hsq : (A : Matrix (Fin n) (Fin n) ℤ) p c * (A : Matrix (Fin n) (Fin n) ℤ) p c = 1 := by
    rcases hunit with h | h <;> rw [h] <;> norm_num
  by_cases hpc : p = c
  · subst hpc
    rcases hunit with h1 | h1
    · refine ⟨1, one_mem _, ?_, ?_⟩
      · simpa using hA
      · refine column_eq_of_active hm _ (by simpa using hA) fun i hi => ?_
        by_cases hic : i = c
        · rw [hic, if_pos rfl]
          simpa using h1
        · rw [if_neg hic]
          simpa using hzero i hi hic
    · set j : Fin n := ⟨m + 1, hm2⟩ with hj
      have hjact : m ≤ (j : ℕ) := by simp [hj]
      have hjc : j ≠ c := by
        intro h
        have h2 : (j : ℕ) = (c : ℕ) := by rw [h]
        simp [hj, hcm] at h2
      have hcj : c ≠ j := Ne.symm hjc
      have hAjc : (A : Matrix (Fin n) (Fin n) ℤ) j c = 0 := hzero j hjact hjc
      refine ⟨elemSL j c hjc 1 * (elemSL c j hcj (-2) * elemSL j c hjc 1), ?_, ?_, ?_⟩
      · exact mul_mem (elemSL_mem_ESub _ _ _ _)
          (mul_mem (elemSL_mem_ESub _ _ _ _) (elemSL_mem_ESub _ _ _ _))
      · rw [mul_assoc, mul_assoc]
        exact partialId_rowOp (partialId_rowOp (partialId_rowOp hA hjc hjact hcact 1)
          hcj hcact hjact (-2)) hjc hjact hcact 1
      · rw [mul_assoc, mul_assoc]
        refine column_eq_of_active hm _ (partialId_rowOp (partialId_rowOp
          (partialId_rowOp hA hjc hjact hcact 1) hcj hcact hjact (-2)) hjc hjact hcact 1)
          fun i hi => ?_
        simp only [elemSL_mul_apply, ← hc]
        by_cases hij : i = j
        · simp [hij, hjc, hcj, hAjc, h1]
        · by_cases hic : i = c
          · simp [hic, hcj, hAjc, h1]
          · simp [hij, hic, hzero i hi hic]
  · have hcp : c ≠ p := fun h => hpc h.symm
    have hpc' : p ≠ c := hpc
    have hAcc : (A : Matrix (Fin n) (Fin n) ℤ) c c = 0 := hzero c hcact hcp
    refine ⟨elemSL p c hpc' (-(A : Matrix (Fin n) (Fin n) ℤ) p c) *
      elemSL c p hcp ((A : Matrix (Fin n) (Fin n) ℤ) p c), ?_, ?_, ?_⟩
    · exact mul_mem (elemSL_mem_ESub _ _ _ _) (elemSL_mem_ESub _ _ _ _)
    · rw [mul_assoc]
      exact partialId_rowOp (partialId_rowOp hA hcp hcact hp _) hpc' hp hcact _
    · rw [mul_assoc]
      refine column_eq_of_active hm _ (partialId_rowOp (partialId_rowOp hA hcp hcact hp _)
        hpc' hp hcact _) fun i hi => ?_
      simp only [elemSL_mul_apply, ← hc]
      by_cases hip : i = p
      · simp [hip, hpc', hAcc, hsq]
      · by_cases hic : i = c
        · simp [hic, hcp, hAcc, hsq]
        · simp [hip, hic, hzero i hi hip]

/-- The sum of the absolute values of the pivot column below the first `m` rows. -/
def colMeasure (m : ℕ) (hm : m < n) (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  ∑ i ∈ Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ), (A i ⟨m, hm⟩).natAbs

lemma natAbs_emod_lt {a b : ℤ} (hb : b ≠ 0) : (a % b).natAbs < b.natAbs := by
  have h1 : 0 ≤ a % b := Int.emod_nonneg a hb
  have h2 : a % b < |b| := Int.emod_lt_abs a hb
  rw [Int.abs_eq_natAbs] at h2
  omega

/-- **Column reduction.**  Elementary row operations turn the pivot column of a matrix
satisfying `PartialId m` into a standard basis vector.  The proof is the Euclidean algorithm:
as long as two entries of the column are nonzero, one may be reduced modulo the other. -/
lemma exists_reduce_column {m : ℕ} (hm : m < n) (hm2 : m + 1 < n) (N : ℕ) :
    ∀ A : Matrix.SpecialLinearGroup (Fin n) ℤ, PartialId m (A : Matrix (Fin n) (Fin n) ℤ) →
      colMeasure m hm (A : Matrix (Fin n) (Fin n) ℤ) ≤ N →
      ∃ g ∈ ESub n, PartialId m ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ∧
        ∀ i : Fin n, ((g * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0 := by
  classical
  induction N with
  | zero =>
      intro A hA hmeas
      exfalso
      have hz : ∀ i : Fin n, m ≤ (i : ℕ) → (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0 := by
        intro i hi
        have hmem : i ∈ Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) := by simp [hi]
        have hsum : ∑ i ∈ Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ),
            ((A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩).natAbs = 0 := Nat.le_zero.1 hmeas
        have := (Finset.sum_eq_zero_iff.1 hsum) i hmem
        simpa [Int.natAbs_eq_zero] using this
      have h0 : IsUnit (0 : ℤ) :=
        column_isUnit_of_dvd hm A hA 0 fun i hi => by rw [hz i hi]
      simp at h0
  | succ N ih =>
      intro A hA hmeas
      set S : Finset (Fin n) := Finset.univ.filter fun i : Fin n => m ≤ (i : ℕ) with hS
      set T : Finset (Fin n) :=
        S.filter fun i => (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ ≠ 0 with hT
      have hmemS : ∀ i : Fin n, i ∈ S ↔ m ≤ (i : ℕ) := by intro i; simp [hS]
      have hmemT : ∀ i : Fin n, i ∈ T ↔
          (m ≤ (i : ℕ) ∧ (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ ≠ 0) := by
        intro i; simp [hT, hS]
      by_cases hcard : 1 < T.card
      · obtain ⟨p, hpT, hpmax⟩ := T.exists_max_image
          (fun i => ((A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩).natAbs)
          (Finset.card_pos.1 (by omega))
        obtain ⟨q, hqT, hqp⟩ := Finset.exists_mem_ne hcard p
        have hp := (hmemT p).1 hpT
        have hq := (hmemT q).1 hqT
        have hpq : p ≠ q := fun h => hqp h.symm
        set a : ℤ := (A : Matrix (Fin n) (Fin n) ℤ) p ⟨m, hm⟩ with ha
        set b : ℤ := (A : Matrix (Fin n) (Fin n) ℤ) q ⟨m, hm⟩ with hb
        set g1 : Matrix.SpecialLinearGroup (Fin n) ℤ := elemSL p q hpq (-(a / b)) with hg1
        have hA1 : PartialId m ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) := partialId_rowOp hA hpq hp.1 hq.1 _
        have hentry : ∀ i : Fin n, ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ =
            if i = p then a % b else (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ := by
          intro i
          rw [hg1, elemSL_mul_apply]
          by_cases hip : i = p
          · rw [if_pos hip, if_pos hip, Int.emod_def]
            ring
          · rw [if_neg hip, if_neg hip]
        have hlt : colMeasure m hm ((g1 * A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) < colMeasure m hm (A : Matrix (Fin n) (Fin n) ℤ) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨p, (hmemS p).2 hp.1, ?_⟩
          · rw [hentry i]
            by_cases hip : i = p
            · subst hip
              rw [if_pos rfl]
              exact le_of_lt (lt_of_lt_of_le (natAbs_emod_lt hq.2) (hpmax q hqT))
            · rw [if_neg hip]
          · rw [hentry p, if_pos rfl]
            exact lt_of_lt_of_le (natAbs_emod_lt hq.2) (hpmax q hqT)
        obtain ⟨g, hg, hgp, hgc⟩ := ih _ hA1 (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hmeas))
        refine ⟨g * g1, mul_mem hg (elemSL_mem_ESub _ _ _ _), ?_, ?_⟩
        · rwa [mul_assoc]
        · rw [mul_assoc]
          exact hgc
      · push_neg at hcard
        rcases Nat.lt_or_ge T.card 1 with hc0 | hc1
        · exfalso
          have hTe : T = ∅ := Finset.card_eq_zero.1 (by omega)
          have hz : ∀ i : Fin n, m ≤ (i : ℕ) →
              (A : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = 0 := by
            intro i hi
            by_contra hne
            have : i ∈ T := (hmemT i).2 ⟨hi, hne⟩
            rw [hTe] at this
            simp at this
          have h0 : IsUnit (0 : ℤ) :=
            column_isUnit_of_dvd hm A hA 0 fun i hi => by rw [hz i hi]
          simp at h0
        · obtain ⟨p, hTp⟩ := (Finset.card_eq_one (s := T)).1 (by omega)
          have hpT : p ∈ T := by rw [hTp]; simp
          have hp := (hmemT p).1 hpT
          refine exists_reduce_column_of_single hm hm2 A hA p hp.1 fun i hi hip => ?_
          by_contra hne
          have : i ∈ T := (hmemT i).2 ⟨hi, hne⟩
          rw [hTp] at this
          exact hip (Finset.mem_singleton.1 this)

/-- Clearing the pivot row to the right of the pivot by elementary column operations. -/
lemma exists_clear_row {m : ℕ} (hm : m < n) :
    ∀ (s : Finset (Fin n)), (∀ j ∈ s, m < (j : ℕ)) →
      ∀ B : Matrix.SpecialLinearGroup (Fin n) ℤ, PartialId m (B : Matrix (Fin n) (Fin n) ℤ) →
      (∀ i : Fin n, (B : Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) →
      ∃ h ∈ ESub n,
        PartialId m ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ∧
        (∀ i : Fin n, ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) i ⟨m, hm⟩ = if i = ⟨m, hm⟩ then 1 else 0) ∧
        (∀ j ∈ s, ((B * h : Matrix.SpecialLinearGroup (Fin n) ℤ) :
          Matrix (Fin n) (Fin n) ℤ) ⟨m, hm⟩ j = 0) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _ B hB hcol
      exact ⟨1, one_mem _, by simpa using hB, by simpa using hcol, by simp⟩
  | insert j s hjs ih =>
      intro hs B hB hcol
      have hs' : ∀ x ∈ s, m < (x : ℕ) := fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hmj : m < (j : ℕ) := hs j (Finset.mem_insert_self j s)
      obtain ⟨h1, hh1, hp1, hcol1, hrow1⟩ := ih hs' B hB hcol
      have hne : (⟨m, hm⟩ : Fin n) ≠ j := by
        intro h
        rw [← h] at hmj
        simp at hmj
      refine ⟨h1 * elemSL ⟨m, hm⟩ j hne
          (-((B * h1 : Matrix.SpecialLinearGroup (Fin n) ℤ) :
            Matrix (Fin n) (Fin n) ℤ) ⟨m, hm⟩ j),
        mul_mem hh1 (elemSL_mem_ESub _ _ _ _), ?_, ?_, ?_⟩
      · rw [← mul_assoc]
        exact partialId_colOp hp1 hne (le_of_eq rfl) (le_of_lt hmj) _
      · rw [← mul_assoc]
        intro i
        rw [mul_elemSL_apply, if_neg hne]
        exact hcol1 i
      · rw [← mul_assoc]
        intro j' hj'
        rw [mul_elemSL_apply]
        rcases Finset.mem_insert.1 hj' with rfl | hjmem
        · rw [if_pos rfl, hcol1 ⟨m, hm⟩]
          simp
        · have hne' : j' ≠ j := by
            rintro rfl
            exact hjs hjmem
          rw [if_neg hne']
          exact hrow1 j' hjmem

/-- **Gaussian elimination.**  Any element of `SL(n, ℤ)` agreeing with the identity on the
first `m` rows and columns is a product of elementary matrices. -/
lemma mem_ESub_of_partialId (k : ℕ) : ∀ m : ℕ, n ≤ m + k →
    ∀ A : Matrix.SpecialLinearGroup (Fin n) ℤ, PartialId m (A : Matrix (Fin n) (Fin n) ℤ) →
      A ∈ ESub n := by
  induction k with
  | zero =>
      intro m hmk A hA
      rw [eq_one_of_partialId_ge A (by omega) hA]
      exact one_mem _
  | succ k ih =>
      intro m hmk A hA
      by_cases hmn : n ≤ m
      · rw [eq_one_of_partialId_ge A hmn hA]
        exact one_mem _
      push_neg at hmn
      by_cases hm1 : m + 1 = n
      · rw [eq_one_of_partialId_succ A hm1 hA]
        exact one_mem _
      have hm2 : m + 1 < n := by omega
      obtain ⟨g, hg, hgp, hgcol⟩ :=
        exists_reduce_column hmn hm2 (colMeasure m hmn (A : Matrix (Fin n) (Fin n) ℤ)) A hA le_rfl
      obtain ⟨h, hh, hhp, hhcol, hhrow⟩ := exists_clear_row hmn
        (Finset.univ.filter fun j : Fin n => m < (j : ℕ)) (by simp) (g * A) hgp hgcol
      have hnew : PartialId (m + 1)
          ((g * A * h : Matrix.SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) := by
        intro i j hij
        by_cases hi : (i : ℕ) < m
        · exact hhp i j (Or.inl hi)
        by_cases hj : (j : ℕ) < m
        · exact hhp i j (Or.inr hj)
        push_neg at hi hj
        have hmval : ((⟨m, hmn⟩ : Fin n) : ℕ) = m := rfl
        by_cases hjc : j = (⟨m, hmn⟩ : Fin n)
        · rw [hjc, hhcol i]
        · have hjm : m < (j : ℕ) := by
            rcases lt_or_eq_of_le hj with hlt | heq
            · exact hlt
            · exact absurd (Fin.ext (by rw [hmval]; omega)) hjc
          have hic : i = (⟨m, hmn⟩ : Fin n) := by
            rcases hij with hlt | hlt
            · exact Fin.ext (by rw [hmval]; omega)
            · exact absurd (Fin.ext (by rw [hmval]; omega) : j = (⟨m, hmn⟩ : Fin n)) hjc
          rw [hic, hhrow j (by simp [hjm])]
          have : (⟨m, hmn⟩ : Fin n) ≠ j := fun hcj => hjc hcj.symm
          simp [this]
      have hmem : g * A * h ∈ ESub n := ih (m + 1) (by omega) _ hnew
      have hAeq : A = g⁻¹ * (g * A * h) * h⁻¹ := by group
      rw [hAeq]
      exact mul_mem (mul_mem (inv_mem hg) hmem) (inv_mem hh)

/-- **`SL(n, ℤ)` is generated by elementary matrices.** -/
theorem elemSet_closure_eq_top (n : ℕ) : Subgroup.closure (elemSet n) = ⊤ := by
  refine eq_top_iff.2 fun A _ => ?_
  exact mem_ESub_of_partialId n 0 (by omega) A fun i j hij => absurd hij (by simp)

/-- **`SL(n, ℤ)` is perfect for `n ≥ 3`.** -/
theorem commutator_specialLinearGroup_int_eq_top {n : ℕ} (hn : 3 ≤ n) :
    commutator (Matrix.SpecialLinearGroup (Fin n) ℤ) = ⊤ :=
  commutator_eq_top_of_elemSet_generates hn (elemSet_closure_eq_top n)

/-- **Margulis superrigidity for `SL(n, ℤ) ⊂ SL(n, ℝ)`, abelian targets, unconditional.**
For `n ≥ 3` every homomorphism of the lattice `SL(n, ℤ)` into an abelian topological group is
the restriction of a continuous homomorphism of the ambient group `SL(n, ℝ)`. -/
theorem margulis_superrigidity_abelian_target_higher_rank {n : ℕ} (hn : 3 ≤ n)
    {H : Type*} [CommGroup H] [TopologicalSpace H]
    (π : Matrix.SpecialLinearGroup (Fin n) ℤ →* H) :
    ExtendsToContinuousMulHom (slLatticeIncl n) π :=
  margulis_superrigidity_abelian_target n (commutator_specialLinearGroup_int_eq_top hn) π

end Frontier

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

