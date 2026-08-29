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
def cutSlice (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (a : α) : EuclideanSpace ℂ Ya :=
  WithLp.toLp 2 fun y => f (e.symm (a, y))

omit [Fintype X] [Fintype α] [Fintype Ya] in
@[simp] lemma cutSlice_apply (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (a : α) (y : Ya) :
    cutSlice e f a y = f (e.symm (a, y)) := rfl

/-- `psiv e f u = ∑ a, conj (u a) • cutSlice e f a`. -/
def psiv (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (u : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ Ya :=
  ∑ a, conj (u a) • cutSlice e f a

omit [Fintype X] in
lemma psiv_apply (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (u : EuclideanSpace ℂ α) (y : Ya) :
    psiv e f u y = ∑ a, conj (u a) * f (e.symm (a, y)) := by
  simp [psiv]

omit [Fintype X] in
lemma psiv_add (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (u v : EuclideanSpace ℂ α) :
    psiv e f (u + v) = psiv e f u + psiv e f v := by
  ext y; simp [psiv_apply, add_mul, Finset.sum_add_distrib]

omit [Fintype X] in
lemma psiv_smul (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X) (c : ℂ) (u : EuclideanSpace ℂ α) :
    psiv e f (c • u) = conj c • psiv e f u := by
  ext y; simp [psiv_apply, Finset.mul_sum, mul_assoc]

omit [Fintype X] in
lemma psiv_sum {ζ : Type*} [Fintype ζ] (e : X ≃ α × Ya) (f : EuclideanSpace ℂ X)
    (x : ζ → EuclideanSpace ℂ α) :
    psiv e f (∑ t, x t) = ∑ t, psiv e f (x t) := by
  ext y
  simp only [psiv_apply, WithLp.ofLp_sum, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The null space of the cut `e` for the code `C`: those `u` for which all the vectors
`psiv e f u`, `f ∈ C`, vanish.  Its orthogonal complement has dimension the rank of the
reduced density matrix of the code on the `α` factor. -/
def nullSp (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) :
    Submodule ℂ (EuclideanSpace ℂ α) where
  carrier := {u | ∀ f ∈ C, psiv e f u = 0}
  add_mem' := by intro u v hu hv f hf; simp [psiv_add, hu f hf, hv f hf]
  zero_mem' := by intro f _; ext y; simp [psiv_apply]
  smul_mem' := by intro c u hu f hf; simp [psiv_smul, hu f hf]

lemma mem_nullSp {e : X ≃ α × Ya} {C : Submodule ℂ (EuclideanSpace ℂ X)}
    {u : EuclideanSpace ℂ α} : u ∈ nullSp e C ↔ ∀ f ∈ C, psiv e f u = 0 := Iff.rfl

/-- The rank of the cut: the dimension of the orthogonal complement of the null space. -/
def cutRank (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) : ℕ :=
  finrank ℂ ((nullSp e C)ᗮ)

/-- The span of all slices of codewords along the cut `e`. -/
def cutSpan (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) :
    Submodule ℂ (EuclideanSpace ℂ Ya) :=
  Submodule.span ℂ {v | ∃ f ∈ C, ∃ a, v = cutSlice e f a}

/-- The Knill–Laflamme (erasure) correctability condition for the cut `e`, expressed on
matrix units. -/
def CorrCut (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) : Prop :=
  ∃ lam : α → α → ℂ, ∀ f ∈ C, ∀ g ∈ C, ∀ a a' : α,
    ∑ y : Ya, conj (f (e.symm (a, y))) * g (e.symm (a', y)) = lam a a' * inner ℂ f g

omit [Fintype X] [Fintype α] in
lemma inner_cutSlice (e : X ≃ α × Ya) (f g : EuclideanSpace ℂ X) (a a' : α) :
    (inner ℂ (cutSlice e f a) (cutSlice e g a') : ℂ)
      = ∑ y : Ya, conj (f (e.symm (a, y))) * g (e.symm (a', y)) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma inner_psiv (e : X ≃ α × Ya) {C : Submodule ℂ (EuclideanSpace ℂ X)} {lam : α → α → ℂ}
    (h : ∀ f ∈ C, ∀ g ∈ C, ∀ a a' : α,
      ∑ y : Ya, conj (f (e.symm (a, y))) * g (e.symm (a', y)) = lam a a' * inner ℂ f g)
    {f g : EuclideanSpace ℂ X} (hf : f ∈ C) (hg : g ∈ C) (u w : EuclideanSpace ℂ α) :
    (inner ℂ (psiv e f u) (psiv e g w) : ℂ)
      = (∑ a, ∑ a', u a * conj (w a') * lam a a') * inner ℂ f g := by
  simp only [psiv, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_cutSlice, h f hf g hg, RingHomCompTriple.comp_apply, RingHom.id_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by ring

lemma psiv_mem_cutSpan (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X))
    {f : EuclideanSpace ℂ X} (hf : f ∈ C) (u : EuclideanSpace ℂ α) :
    psiv e f u ∈ cutSpan e C := by
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f, hf, a, rfl⟩

/-- First half of the argument: correctability of the cut `e` gives
`dim C * rank(e) ≤ dim (span of the slices)`. -/
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
def sliceAt (hA : Ya ≃ β × γ) (c : γ) : EuclideanSpace ℂ Ya →ₗ[ℂ] EuclideanSpace ℂ β where
  toFun v := WithLp.toLp 2 fun b => v (hA.symm (b, c))
  map_add' x y := by ext b; simp
  map_smul' r x := by ext b; simp

omit [Fintype γ] in
@[simp] lemma sliceAt_apply (hA : Ya ≃ β × γ) (c : γ) (v : EuclideanSpace ℂ Ya) (b : β) :
    sliceAt hA c v b = v (hA.symm (b, c)) := rfl

omit [Fintype α] in
/-- Second half of the argument: the span of the slices along the `α`-cut embeds into
`γ`-many copies of the orthogonal complement of the null space of the `β`-cut. -/
lemma finrank_cutSpan_le (eA : X ≃ α × Ya) (eB : X ≃ β × Yb)
    (hA : Ya ≃ β × γ) (hB : Yb ≃ α × γ)
    (compat : ∀ (a : α) (b : β) (c : γ), eA.symm (a, hA.symm (b, c)) = eB.symm (b, hB.symm (a, c)))
    (C : Submodule ℂ (EuclideanSpace ℂ X)) :
    finrank ℂ (cutSpan eA C) ≤ Fintype.card γ * cutRank eB C := by
  have hmem : ∀ v ∈ cutSpan eA C, ∀ c : γ, sliceAt hA c v ∈ (nullSp eB C)ᗮ := by
    intro v hv c
    have hsub : cutSpan eA C ≤ Submodule.comap (sliceAt hA c) ((nullSp eB C)ᗮ) := by
      rw [cutSpan, Submodule.span_le]
      rintro x ⟨f, hf, a, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_orthogonal]
      intro u hu
      have h0 : psiv eB f u = 0 := hu f hf
      have hval : (inner ℂ u (sliceAt hA c (cutSlice eA f a)) : ℂ)
          = psiv eB f u (hB.symm (a, c)) := by
        rw [psiv_apply]
        simp [PiLp.inner_apply, RCLike.inner_apply, compat a _ c, mul_comm]
      rw [hval, h0]
      simp
    exact hsub hv
  let L : ↥(cutSpan eA C) →ₗ[ℂ] (γ → ↥((nullSp eB C)ᗮ)) :=
    { toFun := fun v c => ⟨sliceAt hA c (v : EuclideanSpace ℂ Ya), hmem v v.2 c⟩
      map_add' := by intro v w; funext c; apply Subtype.ext; simp
      map_smul' := by intro r v; funext c; apply Subtype.ext; simp }
  have hinj : Function.Injective L := by
    intro v w h
    apply Subtype.ext
    ext y
    have h1 := congrFun h (hA y).2
    have h2 := congrArg (fun z : ↥((nullSp eB C)ᗮ) => (z : EuclideanSpace ℂ β) (hA y).1) h1
    simpa [L] using h2
  calc finrank ℂ ↥(cutSpan eA C) ≤ finrank ℂ (γ → ↥((nullSp eB C)ᗮ)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card γ * cutRank eB C := by
        simp [Module.finrank_pi_fintype, cutRank]

lemma cutRank_pos (e : X ≃ α × Ya) (C : Submodule ℂ (EuclideanSpace ℂ X)) (hC : C ≠ ⊥) :
    0 < cutRank e C := by
  rcases Nat.eq_zero_or_pos (cutRank e C) with h | h
  · exfalso
    have hbot : (nullSp e C)ᗮ = ⊥ := Submodule.finrank_eq_zero.mp h
    have htop : nullSp e C = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
    refine hC (le_bot_iff.mp fun f hf => ?_)
    have hslice : ∀ a, cutSlice e f a = 0 := by
      intro a
      have hu : (EuclideanSpace.single a (1 : ℂ)) ∈ nullSp e C := by rw [htop]; trivial
      have h0 := hu f hf
      ext y
      have h1 := congrArg (fun v : EuclideanSpace ℂ Ya => v y) h0
      simpa [psiv_apply, EuclideanSpace.single_apply] using h1
    have hf0 : f = 0 := by
      ext x
      have h1 := congrArg (fun v : EuclideanSpace ℂ Ya => v (e x).2) (hslice (e x).1)
      simpa [cutSlice] using h1
    exact Submodule.mem_bot ℂ |>.mpr hf0
  · exact h

/-- The key inequality: `dim C * rank(A-cut) ≤ |γ| * rank(B-cut)`. -/
lemma key_ineq (eA : X ≃ α × Ya) (eB : X ≃ β × Yb)
    (hA : Ya ≃ β × γ) (hB : Yb ≃ α × γ)
    (compat : ∀ (a : α) (b : β) (c : γ), eA.symm (a, hA.symm (b, c)) = eB.symm (b, hB.symm (a, c)))
    (C : Submodule ℂ (EuclideanSpace ℂ X)) (hcA : CorrCut eA C) :
    finrank ℂ C * cutRank eA C ≤ Fintype.card γ * cutRank eB C :=
  le_trans (finrank_mul_cutRank_le eA C hcA) (finrank_cutSpan_le eA eB hA hB compat C)

/-- The abstract core of the quantum Singleton bound: if two "complementary" cuts of a code
are both correctable, the dimension of the code is at most the number of configurations of
the remaining factor. -/
theorem core_bound (eA : X ≃ α × Ya) (eB : X ≃ β × Yb)
    (hA : Ya ≃ β × γ) (hB : Yb ≃ α × γ)
    (compat : ∀ (a : α) (b : β) (c : γ), eA.symm (a, hA.symm (b, c)) = eB.symm (b, hB.symm (a, c)))
    (C : Submodule ℂ (EuclideanSpace ℂ X)) (hC : C ≠ ⊥)
    (hcA : CorrCut eA C) (hcB : CorrCut eB C) :
    finrank ℂ C ≤ Fintype.card γ := by
  have h1 : finrank ℂ C * cutRank eA C ≤ Fintype.card γ * cutRank eB C :=
    key_ineq eA eB hA hB compat C hcA
  have h2 : finrank ℂ C * cutRank eB C ≤ Fintype.card γ * cutRank eA C :=
    key_ineq eB eA hB hA (fun b a c => (compat a b c).symm) C hcB
  have hxa : 0 < cutRank eA C := cutRank_pos eA C hC
  have hxb : 0 < cutRank eB C := cutRank_pos eB C hC
  set K := finrank ℂ C
  set g := Fintype.card γ
  set x := cutRank eA C
  set y := cutRank eB C
  have hmul : (K * x) * (K * y) ≤ (g * y) * (g * x) := Nat.mul_le_mul h1 h2
  have hmul' : (K * K) * (x * y) ≤ (g * g) * (x * y) := by
    calc (K * K) * (x * y) = (K * x) * (K * y) := by ring
    _ ≤ (g * y) * (g * x) := hmul
    _ = (g * g) * (x * y) := by ring
  have hpos : 0 < x * y := Nat.mul_pos hxa hxb
  have hKg : K * K ≤ g * g := Nat.le_of_mul_le_mul_right hmul' hpos
  by_contra hcon
  push_neg at hcon
  exact absurd hKg (not_le.mpr (Nat.mul_lt_mul_of_lt_of_le hcon (le_of_lt hcon)
    (lt_of_le_of_lt (Nat.zero_le _) hcon)))

end Core

noncomputable section Concrete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Merge a configuration on `A` with a configuration on the complement of `A`. -/
def joinAt (q : ℕ) (A : Finset ι) (a : {i // i ∈ A} → Fin q) (y : {i // i ∉ A} → Fin q) :
    ι → Fin q :=
  fun i => if h : i ∈ A then a ⟨i, h⟩ else y ⟨i, h⟩

/-- Splitting the configurations of all sites into those on `A` and those off `A`. -/
def cutEquiv (q : ℕ) (A : Finset ι) :
    (ι → Fin q) ≃ (({i // i ∈ A} → Fin q) × ({i // i ∉ A} → Fin q)) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => Fin q)

omit [Fintype ι] in
@[simp] lemma cutEquiv_symm_apply (q : ℕ) (A : Finset ι) (a : {i // i ∈ A} → Fin q)
    (y : {i // i ∉ A} → Fin q) : (cutEquiv q A).symm (a, y) = joinAt q A a y := rfl

/-- The Knill–Laflamme erasure-correction condition for the set of sites `A`:
for all codewords `f`, `g` and all "matrix units" `|a⟩⟨a'|` supported on `A`,
`⟪f, (|a⟩⟨a'| ⊗ 1) g⟫ = λ(a, a') ⟪f, g⟫`. -/
def Correctable (q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (ι → Fin q))) (A : Finset ι) : Prop :=
  ∃ lam : ({i // i ∈ A} → Fin q) → ({i // i ∈ A} → Fin q) → ℂ,
    ∀ f ∈ C, ∀ g ∈ C, ∀ a a' : {i // i ∈ A} → Fin q,
      ∑ y : {i // i ∉ A} → Fin q,
        conj (f (joinAt q A a y)) * g (joinAt q A a' y) = lam a a' * inner ℂ f g

lemma corrCut_of_correctable (q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (ι → Fin q)))
    (A : Finset ι) (h : Correctable q C A) : CorrCut (cutEquiv q A) C := h

/-- Every one-dimensional code is correctable for *every* set of sites.  This is why the
hypothesis `1 ≤ k` (equivalently `2 ≤ dim C`) in the Singleton bound below cannot be dropped:
a one-dimensional code has "distance" `n + 1` under the usual convention. -/
lemma correctable_span_singleton (q : ℕ) (f : EuclideanSpace ℂ (ι → Fin q)) (hf : f ≠ 0)
    (A : Finset ι) : Correctable q (Submodule.span ℂ {f}) A := by
  refine ⟨fun a a' => (∑ y : {i // i ∉ A} → Fin q,
      conj (f (joinAt q A a y)) * f (joinAt q A a' y)) / (inner ℂ f f), ?_⟩
  intro g hg g' hg' a a'
  rw [Submodule.mem_span_singleton] at hg hg'
  obtain ⟨c, rfl⟩ := hg
  obtain ⟨c', rfl⟩ := hg'
  have hff : (inner ℂ f f : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hf
  have hL : ∑ y : {i // i ∉ A} → Fin q,
      conj ((c • f) (joinAt q A a y)) * ((c' • f) (joinAt q A a' y))
      = conj c * c' * ∑ y : {i // i ∉ A} → Fin q,
          conj (f (joinAt q A a y)) * f (joinAt q A a' y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hL, inner_smul_left, inner_smul_right]
  field_simp

/-- Split the configurations off `A` into those on `B` and those off both. -/
def splitCompl (q : ℕ) (A B : Finset ι) (hAB : Disjoint A B) :
    ({i // i ∉ A} → Fin q) ≃ (({i // i ∈ B} → Fin q) × ({i // i ∉ A ∧ i ∉ B} → Fin q)) where
  toFun y := (fun j => y ⟨j.1, fun hj => Finset.disjoint_left.mp hAB hj j.2⟩,
    fun j => y ⟨j.1, j.2.1⟩)
  invFun p := fun j => if h : j.1 ∈ B then p.1 ⟨j.1, h⟩ else p.2 ⟨j.1, ⟨j.2, h⟩⟩
  left_inv := by
    intro y; funext j
    by_cases h : j.1 ∈ B <;> simp [h]
  right_inv := by
    intro p
    ext j
    · simp [j.2]
    · simp [j.2.2]

/-- Split the configurations off `B` into those on `A` and those off both. -/
def splitCompl' (q : ℕ) (A B : Finset ι) (hAB : Disjoint A B) :
    ({i // i ∉ B} → Fin q) ≃ (({i // i ∈ A} → Fin q) × ({i // i ∉ A ∧ i ∉ B} → Fin q)) where
  toFun y := (fun j => y ⟨j.1, fun hj => Finset.disjoint_left.mp hAB j.2 hj⟩,
    fun j => y ⟨j.1, j.2.2⟩)
  invFun p := fun j => if h : j.1 ∈ A then p.1 ⟨j.1, h⟩ else p.2 ⟨j.1, ⟨h, j.2⟩⟩
  left_inv := by
    intro y; funext j
    by_cases h : j.1 ∈ A <;> simp [h]
  right_inv := by
    intro p
    ext j
    · simp [j.2]
    · simp [j.2.1]

omit [Fintype ι] in
lemma split_compat (q : ℕ) (A B : Finset ι) (hAB : Disjoint A B)
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i // i ∉ A ∧ i ∉ B} → Fin q) :
    (cutEquiv q A).symm (a, (splitCompl q A B hAB).symm (b, c))
      = (cutEquiv q B).symm (b, (splitCompl' q A B hAB).symm (a, c)) := by
  funext i
  by_cases hA : i ∈ A
  · have hB : i ∉ B := Finset.disjoint_left.mp hAB hA
    simp [joinAt, splitCompl, splitCompl', hA, hB]
  · by_cases hB : i ∈ B <;> simp [joinAt, splitCompl, splitCompl', hA, hB]

/-- Dimension bound for a code with two disjoint correctable sets of sites. -/
theorem finrank_le_of_two_correctable (q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (ι → Fin q)))
    (hC : C ≠ ⊥) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : Correctable q C A) (hB : Correctable q C B) :
    finrank ℂ C ≤ q ^ (Fintype.card ι - A.card - B.card) := by
  have hcard : Fintype.card ({i : ι // i ∉ A ∧ i ∉ B} → Fin q)
      = q ^ (Fintype.card ι - A.card - B.card) := by
    have h1 : Fintype.card {i : ι // i ∉ A ∧ i ∉ B} = Fintype.card ι - A.card - B.card := by
      have h2 : Fintype.card {i : ι // i ∉ A ∧ i ∉ B} = ((A ∪ B)ᶜ : Finset ι).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext i
        simp
      rw [h2, Finset.card_compl, Finset.card_union_of_disjoint hAB]
      omega
    rw [Fintype.card_fun, h1, Fintype.card_fin]
  rw [← hcard]
  exact core_bound (cutEquiv q A) (cutEquiv q B) (splitCompl q A B hAB) (splitCompl' q A B hAB)
    (split_compat q A B hAB) C hC (corrCut_of_correctable q C A hA) (corrCut_of_correctable q C B hB)

end Concrete

/-- **Quantum Singleton bound**, strong form: an `[[n, k, d]]_q` code with `q ≥ 2` and `k ≥ 1`
satisfies `k + 2 (d - 1) ≤ n`. -/
theorem quantum_singleton' {q n k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (C : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin q)))
    (hdim : finrank ℂ C = q ^ k)
    (hcorr : ∀ A : Finset (Fin n), A.card ≤ d - 1 → Correctable q C A) :
    k + 2 * (d - 1) ≤ n := by
  set t := d - 1 with ht
  have hq1 : 1 < q := hq
  have hCne : C ≠ ⊥ := by
    intro h
    rw [h] at hdim
    simp only [finrank_bot] at hdim
    have hpos : 0 < q ^ k := Nat.pow_pos (by omega)
    omega
  -- choose two disjoint sets of sites, each of size at most `t`
  obtain ⟨A, -, hAcard⟩ :=
    Finset.le_card_iff_exists_subset_card.mp
      (show min t n ≤ (Finset.univ : Finset (Fin n)).card by
        rw [Finset.card_univ, Fintype.card_fin]; exact min_le_right _ _)
  obtain ⟨B, hBsub, hBcard⟩ :=
    Finset.le_card_iff_exists_subset_card.mp
      (show min t (n - min t n) ≤ (Aᶜ : Finset (Fin n)).card by
        rw [Finset.card_compl, hAcard]
        simp only [Fintype.card_fin]
        exact min_le_right _ _)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact (Finset.mem_compl.mp (hBsub hiB)) hiA
  have hcA : Correctable q C A := hcorr A (by rw [hAcard]; exact min_le_left _ _)
  have hcB : Correctable q C B := hcorr B (by rw [hBcard]; exact min_le_left _ _)
  have hbound := finrank_le_of_two_correctable q C hCne A B hAB hcA hcB
  rw [hdim, hAcard, hBcard] at hbound
  simp only [Fintype.card_fin] at hbound
  have hk' : k ≤ n - min t n - min t (n - min t n) := (Nat.pow_le_pow_iff_right hq1).mp hbound
  omega

/-- **Quantum Singleton bound**: an `[[n, k, d]]_q` quantum code (`q ≥ 2`, `k ≥ 1`) obeys
`n - k ≥ 2 (d - 1)`. -/
theorem quantum_singleton {q n k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (C : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin q)))
    (hdim : finrank ℂ C = q ^ k)
    (hcorr : ∀ A : Finset (Fin n), A.card ≤ d - 1 → Correctable q C A) :
    2 * (d - 1) ≤ n - k := by
  have h := quantum_singleton' hq hk C hdim hcorr
  omega

end QI

