/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space `V`: an antiunitary
(antilinear, inner-product-conjugating) involution-up-to-sign with `Θ ∘ Θ = -1`,
which is the situation of a half-integer-spin system. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  /-- Additivity. -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- Antilinearity. -/
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- Antiunitarity: `⟪Θ x, Θ y⟫ = conj ⟪x, y⟫ = ⟪y, x⟫`. -/
  inner_map' : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- Half-integer spin: `Θ² = -1`. -/
  sq_eq_neg' : ∀ x, toFun (toFun x) = -x

namespace TimeReversal

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

variable (Θ : TimeReversal V)

@[simp] lemma map_add (x y : V) : Θ (x + y) = Θ x + Θ y := Θ.map_add' x y

@[simp] lemma map_smul (c : ℂ) (x : V) : Θ (c • x) = (starRingEnd ℂ) c • Θ x := Θ.map_smul' c x

@[simp] lemma inner_map (x y : V) : ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ := Θ.inner_map' x y

@[simp] lemma sq_eq_neg (x : V) : Θ (Θ x) = -x := Θ.sq_eq_neg' x

@[simp] lemma map_zero : Θ 0 = 0 := by
  have := Θ.map_smul' 0 0
  simpa using this

lemma map_ne_zero {x : V} (hx : x ≠ 0) : Θ x ≠ 0 := by
  intro h
  apply hx
  have : Θ (Θ x) = 0 := by rw [h]; exact Θ.map_zero
  rw [Θ.sq_eq_neg] at this
  simpa using this

/-- The Kramers orthogonality relation: a vector is always orthogonal to its time reverse. -/
lemma inner_self_time_reverse (x : V) : ⟪x, Θ x⟫_ℂ = 0 := by
  have h := Θ.inner_map (Θ x) x
  rw [Θ.sq_eq_neg, inner_neg_left] at h
  linear_combination (-1/2 : ℂ) * h

end TimeReversal

/-- Two nonzero orthogonal vectors are linearly independent. -/
lemma linearIndependent_pair_of_inner_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ⟪x, y⟫_ℂ = 0) : LinearIndependent ℂ ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : ⟪x, s • x + t • y⟫_ℂ = 0 := by rw [hst]; simp
  have h2 : ⟪y, s • x + t • y⟫_ℂ = 0 := by rw [hst]; simp
  rw [inner_add_right, inner_smul_right, inner_smul_right, h] at h1
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    show ⟪y, x⟫_ℂ = 0 by rw [← inner_conj_symm, h]; simp] at h2
  simp only [mul_zero, add_zero, zero_add] at h1 h2
  have hx' : (⟪x, x⟫_ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hx
  have hy' : (⟪y, y⟫_ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hy
  exact ⟨by simpa [hx', hx] using h1, by simpa [hy', hy] using h2⟩

/--
**Kramers degeneracy.**  Let `H` be the Hamiltonian of a system with a time-reversal
symmetry `Θ` satisfying `Θ² = -1` (half-integer total spin), i.e. `Θ ∘ H = H ∘ Θ`.
Then every (real) energy level `E` of `H` is at least doubly degenerate: the eigenspace
of `H` for `E` has rank at least `2`.  Concretely, an eigenvector `ψ` and its time
reverse `Θ ψ` are nonzero, orthogonal, linearly independent eigenvectors for the same
energy.
-/
theorem kramers_degeneracy (Θ : TimeReversal V) (H : V →ₗ[ℂ] V)
    (hcomm : ∀ x, Θ (H x) = H (Θ x)) (E : ℝ) (ψ : V) (hψ : ψ ≠ 0)
    (heig : H ψ = (E : ℂ) • ψ) :
    (Θ ψ ≠ 0 ∧ H (Θ ψ) = (E : ℂ) • Θ ψ ∧ ⟪ψ, Θ ψ⟫_ℂ = 0 ∧
      LinearIndependent ℂ ![ψ, Θ ψ]) ∧
    2 ≤ Module.rank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  have hne : Θ ψ ≠ 0 := Θ.map_ne_zero hψ
  have hEig2 : H (Θ ψ) = (E : ℂ) • Θ ψ := by
    rw [← hcomm, heig, Θ.map_smul]
    simp
  have horth : ⟪ψ, Θ ψ⟫_ℂ = 0 := Θ.inner_self_time_reverse ψ
  have hli : LinearIndependent ℂ ![ψ, Θ ψ] :=
    linearIndependent_pair_of_inner_eq_zero hψ hne horth
  refine ⟨⟨hne, hEig2, horth, hli⟩, ?_⟩
  -- transfer the linear independence into the eigenspace
  have hmem1 : ψ ∈ Module.End.eigenspace H (E : ℂ) := by
    simp [heig]
  have hmem2 : Θ ψ ∈ Module.End.eigenspace H (E : ℂ) := by
    simp [hEig2]
  set W := Module.End.eigenspace H (E : ℂ)
  set b : Fin 2 → W := ![⟨ψ, hmem1⟩, ⟨Θ ψ, hmem2⟩] with hb
  have hbli : LinearIndependent ℂ b := by
    apply LinearIndependent.of_comp W.subtype
    convert hli using 1
    funext i
    fin_cases i <;> simp [hb]
  have := hbli.cardinal_lift_le_rank
  simpa using this

namespace TimeReversal

variable (Θ : TimeReversal V)

/-- If every generator of a span has its time reverse in the span, the whole span is
`Θ`-invariant. -/
lemma span_invariant {s : Set V} (h : ∀ x ∈ s, Θ x ∈ Submodule.span ℂ s) :
    ∀ x ∈ Submodule.span ℂ s, Θ x ∈ Submodule.span ℂ s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp
  | add u v _ _ ihu ihv => rw [Θ.map_add]; exact Submodule.add_mem _ ihu ihv
  | smul c u _ ih => rw [Θ.map_smul]; exact Submodule.smul_mem _ _ ih

/-- The orthogonal complement of a `Θ`-invariant subspace is `Θ`-invariant. -/
lemma orthogonal_invariant {U : Submodule ℂ V} (hU : ∀ x ∈ U, Θ x ∈ U) :
    ∀ x ∈ Uᗮ, Θ x ∈ Uᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  have h1 : ⟪Θ (Θ u), Θ x⟫_ℂ = ⟪x, Θ u⟫_ℂ := Θ.inner_map _ _
  rw [Θ.sq_eq_neg, inner_neg_left] at h1
  have h2 : ⟪Θ u, x⟫_ℂ = 0 := hx _ (hU u hu)
  have h3 : ⟪x, Θ u⟫_ℂ = 0 := by
    rw [← inner_conj_symm, h2]
    simp
  rw [h3] at h1
  linear_combination (norm := ring_nf) -h1

/-- **Even degeneracy.** In a finite-dimensional space, every `Θ`-invariant subspace has
even dimension, when `Θ² = -1`.  This is the strong form of Kramers' theorem, proved by
strong induction on the dimension: one splits off the two-dimensional `Θ`-invariant plane
spanned by `ψ` and `Θ ψ`. -/
lemma even_finrank_of_invariant [FiniteDimensional ℂ V] :
    ∀ n : ℕ, ∀ U : Submodule ℂ V, Module.finrank ℂ U = n → (∀ x ∈ U, Θ x ∈ U) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hUrank hinv
    rcases eq_or_ne n 0 with h0 | h0
    · simp [h0]
    have hUne : U ≠ ⊥ := by
      rintro rfl
      simp at hUrank
      exact h0 hUrank.symm
    obtain ⟨ψ, hψU, hψ0⟩ := (Submodule.ne_bot_iff U).1 hUne
    have hli : LinearIndependent ℂ ![ψ, Θ ψ] :=
      linearIndependent_pair_of_inner_eq_zero hψ0 (Θ.map_ne_zero hψ0)
        (Θ.inner_self_time_reverse ψ)
    set S : Submodule ℂ V := Submodule.span ℂ (Set.range ![ψ, Θ ψ]) with hS
    have hSrank : Module.finrank ℂ S = 2 := by
      rw [hS, finrank_span_eq_card hli]
      simp
    have hmemψ : ψ ∈ S := Submodule.subset_span ⟨0, rfl⟩
    have hmemΘψ : Θ ψ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    have hSU : S ≤ U := by
      rw [hS, Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hψU
      · exact hinv _ hψU
    have hSinv : ∀ x ∈ S, Θ x ∈ S := by
      refine Θ.span_invariant ?_
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hmemΘψ
      · show Θ (Θ ψ) ∈ S
        rw [Θ.sq_eq_neg]
        exact Submodule.neg_mem _ hmemψ
    have hinv' : ∀ x ∈ Sᗮ ⊓ U, Θ x ∈ Sᗮ ⊓ U := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨Θ.orthogonal_invariant hSinv x hx1, hinv x hx2⟩
    have hsum : Module.finrank ℂ S + Module.finrank ℂ (Sᗮ ⊓ U : Submodule ℂ V)
        = Module.finrank ℂ U := Submodule.finrank_add_inf_finrank_orthogonal hSU
    rw [hSrank, hUrank] at hsum
    have hlt : Module.finrank ℂ (Sᗮ ⊓ U : Submodule ℂ V) < n := by omega
    have := ih _ hlt (Sᗮ ⊓ U) rfl hinv'
    rcases this with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

end TimeReversal

/--
**Kramers degeneracy, strong form.**  In a finite-dimensional state space, for a
half-integer-spin system (`Θ² = -1`) with time-reversal-invariant Hamiltonian `H`,
every energy eigenspace has *even* dimension.  In particular no level is nondegenerate.
-/
theorem kramers_even_degeneracy [FiniteDimensional ℂ V] (Θ : TimeReversal V) (H : V →ₗ[ℂ] V)
    (hcomm : ∀ x, Θ (H x) = H (Θ x)) (E : ℝ) :
    Even (Module.finrank ℂ (Module.End.eigenspace H (E : ℂ))) := by
  refine Θ.even_finrank_of_invariant _ _ rfl ?_
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  rw [← hcomm, hx, Θ.map_smul]
  simp

/-- The hypotheses above are non-vacuous: on the spin-`1/2` state space `ℂ²` the operator
`Θ = -i σ_y K` (complex conjugation `K` followed by `-i σ_y`) is a time-reversal operator
with `Θ² = -1`. -/
noncomputable def spinHalfTimeReversal : TimeReversal (EuclideanSpace ℂ (Fin 2)) where
  toFun x := WithLp.toLp 2 ![-(starRingEnd ℂ) (x 1), (starRingEnd ℂ) (x 0)]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp
  inner_map' x y := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
    ring
  sq_eq_neg' x := by ext i; fin_cases i <;> simp

end Phys

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

