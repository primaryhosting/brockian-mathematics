import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/
def ngonShift (n : ℕ) (t : ZMod n) : NGon n →ₗ[ℂ] NGon n where
  toFun f := fun k => f (k + t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The reflection of the `n`-gon fixing the vertex `0`, acting on functions. -/
def ngonRefl (n : ℕ) : NGon n →ₗ[ℂ] NGon n where
  toFun f := fun k => f (-k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The adjacency operator of the cycle graph on the vertices of the `n`-gon. -/
noncomputable def ngonAdj (n : ℕ) : NGon n →ₗ[ℂ] NGon n := ngonShift n 1 + ngonShift n (-1)

/-- The `j`-th character of the vertex group `ZMod n`, i.e. `k ↦ exp (2πi jk / n)`. -/
noncomputable def ngonChar (n : ℕ) [NeZero n] (j : ZMod n) : AddChar (ZMod n) ℂ :=
  AddChar.mulShift ZMod.stdAddChar j

/-- The `j`-th isotypic component of the vertex space of the `n`-gon for the dihedral
group: the span of the characters `χ_j` and `χ_{-j}`, which are exchanged by the
reflection. -/
noncomputable def ngonIsotypic (n : ℕ) [NeZero n] (j : ZMod n) : Submodule ℂ (NGon n) :=
  Submodule.span ℂ {⇑(ngonChar n j), ⇑(ngonChar n (-j))}

/-- The eigenvalue `2 cos (2π j / n)` of the adjacency operator on the `j`-th isotypic
component.  For `n = 5` these are the two golden-ratio values `(√5-1)/2` and
`-(1+√5)/2`. -/
noncomputable def ngonEigen (n : ℕ) (j : ZMod n) : ℝ := 2 * Real.cos (2 * Real.pi * j.val / n)

section Lemmas

variable {n : ℕ} [NeZero n]

lemma ngonChar_apply (j k : ZMod n) : ngonChar n j k = ZMod.stdAddChar (j * k) := rfl

lemma ngonChar_one (j : ZMod n) : ngonChar n j 1 = ZMod.stdAddChar j := by
  simp [ngonChar_apply]

/-- Each character is an eigenvector of every rotation. -/
lemma ngonShift_char (j t : ZMod n) :
    ngonShift n t ⇑(ngonChar n j) = (ngonChar n j t) • ⇑(ngonChar n j) := by
  funext k
  simp only [ngonShift, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [add_comm k t, AddChar.map_add_eq_mul]

/-- The reflection exchanges `χ_j` and `χ_{-j}`. -/
lemma ngonRefl_char (j : ZMod n) :
    ngonRefl n ⇑(ngonChar n j) = ⇑(ngonChar n (-j)) := by
  funext k
  simp [ngonRefl, ngonChar_apply]

/-- The two characters of the `j`-th isotypic component sum, at the vertex `1`, to the
real number `2 cos (2π j / n)`. -/
lemma ngonChar_add_conj (j : ZMod n) :
    (ngonChar n j 1 : ℂ) + (ngonChar n (-j) 1 : ℂ) = ((ngonEigen n j : ℝ) : ℂ) := by
  rw [ngonChar_one, ngonChar_one]
  set x : ℝ := 2 * Real.pi * j.val / n with hx
  have h1 : (ZMod.stdAddChar j : ℂ) = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hx]
    push_cast; ring_nf
  have h2 : (ZMod.stdAddChar (-j) : ℂ) = Complex.exp (-((x : ℂ) * Complex.I)) := by
    rw [AddChar.map_neg_eq_inv, h1, ← Complex.exp_neg]
  have h3 : ((2 * Real.cos x : ℝ) : ℂ) = 2 * Complex.cos (x : ℂ) := by
    push_cast [Complex.ofReal_cos]; ring
  rw [h1, h2, ngonEigen, ← hx, h3, Complex.two_cos]
  ring_nf

/-- The eigenvalue only depends on the pair `{j, -j}`. -/
lemma ngonEigen_neg (j : ZMod n) : ngonEigen n (-j) = ngonEigen n j := by
  have h := ngonChar_add_conj (n := n) (-j)
  rw [neg_neg, add_comm] at h
  have := (ngonChar_add_conj (n := n) j).symm.trans h
  exact_mod_cast this.symm

/-- Each character is an eigenvector of the adjacency operator, with eigenvalue
`2 cos (2π j / n)`. -/
lemma ngonAdj_char (j : ZMod n) :
    ngonAdj n ⇑(ngonChar n j) = ((ngonEigen n j : ℝ) : ℂ) • ⇑(ngonChar n j) := by
  have hneg : (ngonChar n j (-1) : ℂ) = ngonChar n (-j) 1 := by
    simp [ngonChar_apply]
  rw [ngonAdj, LinearMap.add_apply, ngonShift_char, ngonShift_char, hneg,
    ← add_smul, ngonChar_add_conj]

/-- Membership in the isotypic component can be checked on the two generating
characters. -/
lemma ngonIsotypic_induction {j : ZMod n} {p : NGon n → Prop} (hzero : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ (c : ℂ) a, p a → p (c • a))
    (hj : p ⇑(ngonChar n j)) (hj' : p ⇑(ngonChar n (-j)))
    {f : NGon n} (hf : f ∈ ngonIsotypic n j) : p f := by
  refine Submodule.span_induction (p := fun x _ => p x) ?_ hzero (fun a b _ _ => hadd a b)
    (fun c a _ => hsmul c a) hf
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hj
  · exact hj'

lemma ngonChar_mem_isotypic (j : ZMod n) : ⇑(ngonChar n j) ∈ ngonIsotypic n j :=
  Submodule.subset_span (by simp)

lemma ngonChar_neg_mem_isotypic (j : ZMod n) : ⇑(ngonChar n (-j)) ∈ ngonIsotypic n j :=
  Submodule.subset_span (by simp)

/-- The isotypic component is invariant under every rotation. -/
lemma ngonIsotypic_shift_mem (j t : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonShift n t f ∈ ngonIsotypic n j := by
  refine ngonIsotypic_induction (p := fun g => ngonShift n t g ∈ ngonIsotypic n j)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c a ha => by beta_reduce at *; rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ ?_ hf
  · beta_reduce
    rw [ngonShift_char]
    exact Submodule.smul_mem _ _ (ngonChar_mem_isotypic j)
  · beta_reduce
    rw [ngonShift_char]
    exact Submodule.smul_mem _ _ (ngonChar_neg_mem_isotypic j)

/-- The isotypic component is invariant under the reflection. -/
lemma ngonIsotypic_refl_mem (j : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonRefl n f ∈ ngonIsotypic n j := by
  refine ngonIsotypic_induction (p := fun g => ngonRefl n g ∈ ngonIsotypic n j)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c a ha => by beta_reduce at *; rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ ?_ hf
  · beta_reduce
    rw [ngonRefl_char]
    exact ngonChar_neg_mem_isotypic j
  · beta_reduce
    rw [ngonRefl_char, neg_neg]
    exact ngonChar_mem_isotypic j

/-- The adjacency operator acts on the whole `j`-th isotypic component as the scalar
`2 cos (2π j / n)`. -/
lemma ngonAdj_isotypic (j : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonAdj n f = ((ngonEigen n j : ℝ) : ℂ) • f := by
  refine ngonIsotypic_induction
    (p := fun g => ngonAdj n g = ((ngonEigen n j : ℝ) : ℂ) • g)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add, ha, hb, smul_add])
    (fun c a ha => by beta_reduce at *; rw [map_smul, ha, smul_comm]) (ngonAdj_char j) ?_ hf
  beta_reduce
  rw [ngonAdj_char (-j), ngonEigen_neg]

/-- The two characters spanning the `j`-th isotypic component are distinct as soon as
`j ≠ -j`. -/
lemma ngonChar_ne (j : ZMod n) (hj : j ≠ -j) : ngonChar n j ≠ ngonChar n (-j) := by
  intro h
  apply hj
  have h1 : (ZMod.stdAddChar j : ℂ) = ZMod.stdAddChar (-j) := by
    rw [← ngonChar_one, ← ngonChar_one, h]
  exact ZMod.injective_stdAddChar h1

/-- Linear independence of the two characters spanning the isotypic component. -/
lemma ngonChar_linearIndependent (j : ZMod n) (hj : j ≠ -j) :
    LinearIndependent ℂ ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] := by
  have hinj : Function.Injective ![ngonChar n j, ngonChar n (-j)] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [ngonChar_ne j hj, (ngonChar_ne j hj).symm]
  have := (AddChar.linearIndependent (ZMod n) ℂ).comp _ hinj
  have hfun : (DFunLike.coe ∘ ![ngonChar n j, ngonChar n (-j)])
      = ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at this

/-- The isotypic component is two-dimensional when `j ≠ -j`. -/
lemma ngonIsotypic_finrank (j : ZMod n) (hj : j ≠ -j) :
    Module.finrank ℂ (ngonIsotypic n j) = 2 := by
  have hrange : Set.range ![⇑(ngonChar n j), ⇑(ngonChar n (-j))]
      = {⇑(ngonChar n j), ⇑(ngonChar n (-j))} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [ngonIsotypic, ← hrange]
  simpa using finrank_span_eq_card (ngonChar_linearIndependent j hj)

end Lemmas

section Pentagon

/-- The classical pentagon eigenvalue `2 cos (2π/5) = (√5 - 1)/2`. -/
lemma ngonEigen_five_one : ngonEigen 5 1 = (Real.sqrt 5 - 1) / 2 := by
  have hval : (1 : ZMod 5).val = 1 := by decide
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hx : (2 : ℝ) * Real.pi * ((1 : ZMod 5).val : ℝ) / (5 : ℕ) = 2 * (Real.pi / 5) := by
    rw [hval]; push_cast; ring
  rw [ngonEigen, hx, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- The second pentagon eigenvalue `2 cos (4π/5) = -(1 + √5)/2`. -/
lemma ngonEigen_five_two : ngonEigen 5 2 = -(1 + Real.sqrt 5) / 2 := by
  have hval : (2 : ZMod 5).val = 2 := by decide
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hx : (2 : ℝ) * Real.pi * ((2 : ZMod 5).val : ℝ) / (5 : ℕ) = 2 * (2 * (Real.pi / 5)) := by
    rw [hval]; push_cast; ring
  rw [ngonEigen, hx, Real.cos_two_mul, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

end Pentagon

/-- Generalisation of the `D₅` pentagon isotypic decomposition to arbitrary `n`-gons.

For every `n ≥ 1` and every `j : ZMod n`:
* the isotypic component `ngonIsotypic n j = span {χ_j, χ_{-j}}` is invariant under all
  rotations of the `n`-gon and under the reflection, i.e. it is a `D_n`-subrepresentation;
* the cycle adjacency operator acts on it as the scalar `2 cos (2π j / n)`;
* when `j ≠ -j` the two characters are linearly independent, so the component has
  dimension exactly `2` (an irreducible two-dimensional `D_n`-representation).

Specialising to the pentagon `n = 5` recovers the two golden-ratio eigenvalues
`(√5 - 1)/2` (for `j = 1`) and `-(1 + √5)/2` (for `j = 2`). -/
theorem PentagonPentagonIsotypicHigherN :
    (∀ (n : ℕ) [NeZero n] (j : ZMod n),
        (∀ t : ZMod n, ∀ f ∈ ngonIsotypic n j, ngonShift n t f ∈ ngonIsotypic n j) ∧
        (∀ f ∈ ngonIsotypic n j, ngonRefl n f ∈ ngonIsotypic n j) ∧
        (∀ f ∈ ngonIsotypic n j, ngonAdj n f = ((ngonEigen n j : ℝ) : ℂ) • f) ∧
        (j ≠ -j →
          LinearIndependent ℂ ![⇑(ngonChar n j), ⇑(ngonChar n (-j))] ∧
          Module.finrank ℂ (ngonIsotypic n j) = 2))
    ∧ ngonEigen 5 1 = (Real.sqrt 5 - 1) / 2
    ∧ ngonEigen 5 2 = -(1 + Real.sqrt 5) / 2 :=
  ⟨fun _ _ j =>
      ⟨fun t _ hf => ngonIsotypic_shift_mem j t hf,
       fun _ hf => ngonIsotypic_refl_mem j hf,
       fun _ hf => ngonAdj_isotypic j hf,
       fun hj => ⟨ngonChar_linearIndependent j hj, ngonIsotypic_finrank j hj⟩⟩,
    ngonEigen_five_one, ngonEigen_five_two⟩

end Brockian

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

