import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace QPhys

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hamiltonian `ℏω (a† a + ½)` of a one-dimensional quantum harmonic oscillator,
expressed through the annihilation operator `a` and the creation operator `ad = a†`. -/
noncomputable def hamiltonian (hbar omega : ℝ) (a ad : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  ((hbar * omega : ℝ) : ℂ) • (ad ∘ₗ a + ((1 : ℂ) / 2) • LinearMap.id)

lemma hamiltonian_apply (hbar omega : ℝ) (a ad : E →ₗ[ℂ] E) (v : E) :
    hamiltonian hbar omega a ad v
      = ((hbar * omega : ℝ) : ℂ) • (ad (a v) + ((1 : ℂ) / 2) • v) := rfl

section Ladder

variable {a ad : E →ₗ[ℂ] E}

/-- The adjoint relation, read in the other direction. -/
lemma inner_ad_left (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ) (x y : E) :
    ⟪ad x, y⟫_ℂ = ⟪x, a y⟫_ℂ := by
  rw [← inner_conj_symm (𝕜 := ℂ) (ad x) y, ← hadj, inner_conj_symm]

/-- `a†a` acting on an `n`-fold excited state. -/
lemma number_iterate (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {psi0 : E} (ha0 : a psi0 = 0) (n : ℕ) :
    ad (a (ad^[n] psi0)) = (n : ℂ) • (ad^[n] psi0) := by
  induction n with
  | zero => simp [ha0]
  | succ n ih =>
      have hstep : a (ad (ad^[n] psi0)) = ad (a (ad^[n] psi0)) + ad^[n] psi0 := by
        have := hcomm (ad^[n] psi0)
        linear_combination (norm := module) this
      rw [Function.iterate_succ_apply' (f := ⇑ad), hstep, ih]
      push_cast
      rw [map_add, map_smul]
      module

/-- Norms of the excited states: `⟪ψₙ, ψₙ⟫ = n! ⟪ψ₀, ψ₀⟫`. -/
lemma inner_iterate (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {psi0 : E} (ha0 : a psi0 = 0) (n : ℕ) :
    ⟪ad^[n] psi0, ad^[n] psi0⟫_ℂ = (n ! : ℂ) * ⟪psi0, psi0⟫_ℂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : a (ad (ad^[n] psi0)) = ad (a (ad^[n] psi0)) + ad^[n] psi0 := by
        have := hcomm (ad^[n] psi0)
        linear_combination (norm := module) this
      rw [Function.iterate_succ_apply' (f := ⇑ad)]
      rw [inner_ad_left hadj, hstep, number_iterate hcomm ha0 n]
      rw [inner_add_right, inner_smul_right, ih]
      push_cast [Nat.factorial_succ]
      ring

/-- The excited states are nonzero. -/
lemma iterate_ne_zero (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {psi0 : E} (hpsi0 : psi0 ≠ 0) (ha0 : a psi0 = 0) (n : ℕ) :
    ad^[n] psi0 ≠ 0 := by
  intro h
  have h0 : ⟪psi0, psi0⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hpsi0
  have := inner_iterate hadj hcomm ha0 n
  rw [h] at this
  simp only [inner_zero_left] at this
  have hfac : (n ! : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact h0 (by
    rcases mul_eq_zero.mp this.symm with h1 | h1
    · exact absurd h1 hfac
    · exact h1)

/-- An eigenvalue of the number operator `a†a` is a nonnegative real. -/
lemma number_eigenvalue_nonneg (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    {lam : ℂ} {v : E} (hv : v ≠ 0) (h : ad (a v) = lam • v) :
    ∃ r : ℝ, 0 ≤ r ∧ lam = (r : ℂ) := by
  have key : ⟪a v, a v⟫_ℂ = lam * ⟪v, v⟫_ℂ := by
    rw [hadj v (a v), h, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have hvn : (‖v‖ : ℂ) ^ 2 ≠ 0 := by
    simp [pow_eq_zero_iff, norm_eq_zero, hv]
  refine ⟨‖a v‖ ^ 2 / ‖v‖ ^ 2, by positivity, ?_⟩
  push_cast
  rw [eq_div_iff hvn]
  exact key.symm

/-- Lowering: if `v` is an eigenvector of `a†a` with eigenvalue `lam`, then `a v` is an
eigenvector with eigenvalue `lam - 1`. -/
lemma number_lower (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {lam : ℂ} {v : E} (h : ad (a v) = lam • v) :
    ad (a (a v)) = (lam - 1) • (a v) := by
  have h1 := hcomm (a v)
  have h2 : a (ad (a v)) = lam • a v := by rw [h, map_smul]
  have : ad (a (a v)) = a (ad (a v)) - a v := by
    linear_combination (norm := module) -h1
  rw [this, h2]
  module

lemma lower_ne_zero (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    {lam : ℂ} {v : E} (hv : v ≠ 0) (hlam : lam ≠ 0) (h : ad (a v) = lam • v) :
    a v ≠ 0 := by
  intro hav
  have key : ⟪a v, a v⟫_ℂ = lam * ⟪v, v⟫_ℂ := by
    rw [hadj v (a v), h, inner_smul_right]
  rw [hav] at key
  simp only [inner_zero_left] at key
  rcases mul_eq_zero.mp key.symm with h1 | h1
  · exact hlam h1
  · exact hv (by simpa [inner_self_eq_zero] using h1)

/-- Ladder descent: any eigenvalue of the number operator is a natural number. -/
lemma number_eigenvalue_nat_aux (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x) :
    ∀ (k : ℕ) (r : ℝ) (v : E), v ≠ 0 → 0 ≤ r → r < k → ad (a v) = (r : ℂ) • v →
      ∃ n : ℕ, r = n := by
  intro k
  induction k with
  | zero => intro r v _ hr0 hrk _; exact absurd hrk (by push_cast; linarith)
  | succ k ih =>
      intro r v hv hr0 hrk h
      by_cases hr : r = 0
      · exact ⟨0, by simp [hr]⟩
      · have hlam : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr
        have hav : a v ≠ 0 := lower_ne_zero hadj hv hlam h
        have hnext : ad (a (a v)) = ((r - 1 : ℝ) : ℂ) • (a v) := by
          rw [number_lower hcomm h]; push_cast; ring_nf
        obtain ⟨s, hs0, hs⟩ := number_eigenvalue_nonneg hadj hav hnext
        have hrs : r - 1 = s := by exact_mod_cast hs
        have : (0 : ℝ) ≤ r - 1 := by rw [hrs]; exact hs0
        obtain ⟨n, hn⟩ := ih (r - 1) (a v) hav this (by push_cast at hrk ⊢; linarith) hnext
        exact ⟨n + 1, by push_cast; linarith⟩

lemma number_eigenvalue_nat (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    {lam : ℂ} {v : E} (hv : v ≠ 0) (h : ad (a v) = lam • v) :
    ∃ n : ℕ, lam = (n : ℂ) := by
  obtain ⟨r, hr0, hr⟩ := number_eigenvalue_nonneg hadj hv h
  subst hr
  obtain ⟨k, hk⟩ := exists_nat_gt r
  obtain ⟨n, hn⟩ := number_eigenvalue_nat_aux hadj hcomm k r v hv hr0 hk h
  exact ⟨n, by exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hn⟩

end Ladder

/--
**Spectrum of the quantum harmonic oscillator.**

Let `a` be an annihilation operator on a complex inner-product space with creation
operator (adjoint) `ad = a†`, satisfying the canonical commutation relation
`[a, a†] = 1`, and let `psi0 ≠ 0` be a ground state (`a psi0 = 0`).  Then the set of
eigenvalues of the Hamiltonian `H = ℏω (a†a + ½)` is exactly
`{ℏω (n + ½) : n ∈ ℕ}`.

The proof is the standard ladder-operator argument: the states `(a†)ⁿ psi0` are nonzero
eigenvectors with the stated energies, and conversely repeated application of `a` to any
eigenvector would produce a negative eigenvalue of the positive operator `a†a` unless the
eigenvalue is a natural number.
-/
theorem oscillator_spectrum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a ad : E →ₗ[ℂ] E)
    (hadj : ∀ x y : E, ⟪a x, y⟫_ℂ = ⟪x, ad y⟫_ℂ)
    (hcomm : ∀ x : E, a (ad x) - ad (a x) = x)
    (psi0 : E) (hpsi0 : psi0 ≠ 0) (ha0 : a psi0 = 0)
    (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {z : ℂ | ∃ v : E, v ≠ 0 ∧ hamiltonian hbar omega a ad v = z • v}
      = {z : ℂ | ∃ n : ℕ, z = ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ)} := by
  have hne : ((hbar * omega : ℝ) : ℂ) ≠ 0 := by
    have : hbar * omega ≠ 0 := by positivity
    exact_mod_cast this
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, hHv⟩
    rw [hamiltonian_apply] at hHv
    have hkey : ((hbar * omega : ℝ) : ℂ) * (z / ((hbar * omega : ℝ) : ℂ) - 1 / 2)
        = z - ((hbar * omega : ℝ) : ℂ) * (1 / 2) := by
      field_simp
    have hnum : ad (a v) = (z / ((hbar * omega : ℝ) : ℂ) - 1 / 2) • v := by
      refine smul_right_injective E hne ?_
      show ((hbar * omega : ℝ) : ℂ) • ad (a v)
          = ((hbar * omega : ℝ) : ℂ) • ((z / ((hbar * omega : ℝ) : ℂ) - 1 / 2) • v)
      rw [smul_smul, hkey, sub_smul]
      linear_combination (norm := module) hHv
    obtain ⟨n, hn⟩ := number_eigenvalue_nat hadj hcomm hv hnum
    refine ⟨n, ?_⟩
    have h2 : z / ((hbar * omega : ℝ) : ℂ) = (n : ℂ) + 1 / 2 := by linear_combination hn
    rw [div_eq_iff hne] at h2
    rw [h2]
    push_cast
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨ad^[n] psi0, iterate_ne_zero hadj hcomm hpsi0 ha0 n, ?_⟩
    rw [hamiltonian_apply, number_iterate hcomm ha0 n]
    push_cast
    module

/-! ## A concrete model: the (algebraic) Fock space

The hypotheses of `QPhys.oscillator_spectrum` are not vacuous: they are realised by the
finitely supported sequences inside `ℓ²(ℕ, ℂ)`, with the usual ladder operators
`a eₙ = √n eₙ₋₁`, `a† eₙ = √(n+1) eₙ₊₁`.
-/

/-- The Hilbert space `ℓ²(ℕ, ℂ)`. -/
abbrev Lsp := lp (fun _ : ℕ => ℂ) 2

/-- The (algebraic) Fock space: finitely supported sequences inside `ℓ²(ℕ, ℂ)`. -/
def FockSub : Submodule ℂ Lsp where
  carrier := {x | {n | (x : ℕ → ℂ) n ≠ 0}.Finite}
  add_mem' := by
    intro x y hx hy
    refine Set.Finite.subset (hx.union hy) ?_
    intro n hn
    simp only [Set.mem_setOf_eq, lp.coeFn_add, Pi.add_apply] at hn
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    simp [hc.1, hc.2] at hn
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    refine Set.Finite.subset hx ?_
    intro n hn
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hn ⊢
    exact fun h => hn (by simp [h])

/-- Build an element of the Fock space from a finitely supported sequence. -/
def mkFock (f : ℕ → ℂ) (hf : {n | f n ≠ 0}.Finite) : FockSub :=
  ⟨⟨f, (memℓp_zero hf).of_exponent_ge (by norm_num)⟩, hf⟩

@[simp] lemma mkFock_apply (f : ℕ → ℂ) (hf : {n | f n ≠ 0}.Finite) (n : ℕ) :
    ((mkFock f hf : Lsp) : ℕ → ℂ) n = f n := rfl

lemma fock_finite (x : FockSub) : {n | ((x : Lsp) : ℕ → ℂ) n ≠ 0}.Finite := x.2

/-- Coefficients of the annihilation operator. -/
def annihFun (x : FockSub) : ℕ → ℂ := fun n => (Real.sqrt (n + 1) : ℂ) * (x : Lsp) (n + 1)

/-- Coefficients of the creation operator. -/
def creatFun (x : FockSub) : ℕ → ℂ :=
  fun n => Nat.casesOn n 0 (fun m => (Real.sqrt (m + 1) : ℂ) * (x : Lsp) m)

lemma annihFun_finite (x : FockSub) : {n | annihFun x n ≠ 0}.Finite := by
  refine Set.Finite.subset (Set.Finite.preimage (f := fun n : ℕ => n + 1) ?_ (fock_finite x)) ?_
  · exact Set.injOn_of_injective (fun p q h => by omega)
  · intro n hn
    simp only [Set.mem_setOf_eq, annihFun] at hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h; simp [h] at hn

lemma creatFun_finite (x : FockSub) : {n | creatFun x n ≠ 0}.Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun n : ℕ => n + 1) (fock_finite x)) ?_
  intro n hn
  match n with
  | 0 => simp [creatFun] at hn
  | (m + 1) =>
      simp only [Set.mem_setOf_eq, creatFun] at hn
      refine ⟨m, ?_, rfl⟩
      simp only [Set.mem_setOf_eq]
      intro h; simp [h] at hn

/-- The annihilation operator `a` on the Fock space. -/
def annih : FockSub →ₗ[ℂ] FockSub where
  toFun x := mkFock (annihFun x) (annihFun_finite x)
  map_add' x y := by
    apply Subtype.ext; apply lp.ext; funext n; simp [annihFun]; ring
  map_smul' c x := by
    apply Subtype.ext; apply lp.ext; funext n; simp [annihFun]; ring

/-- The creation operator `a†` on the Fock space. -/
def creat : FockSub →ₗ[ℂ] FockSub where
  toFun x := mkFock (creatFun x) (creatFun_finite x)
  map_add' x y := by
    apply Subtype.ext; apply lp.ext; funext n
    match n with
    | 0 => simp [creatFun]
    | (m + 1) => simp [creatFun]; ring
  map_smul' c x := by
    apply Subtype.ext; apply lp.ext; funext n
    match n with
    | 0 => simp [creatFun]
    | (m + 1) => simp [creatFun]; ring

@[simp] lemma annih_apply (x : FockSub) (n : ℕ) :
    ((annih x : FockSub) : Lsp) n = (Real.sqrt (n + 1) : ℂ) * (x : Lsp) (n + 1) := rfl

@[simp] lemma creat_apply_zero (x : FockSub) : ((creat x : FockSub) : Lsp) 0 = 0 := rfl

@[simp] lemma creat_apply_succ (x : FockSub) (m : ℕ) :
    ((creat x : FockSub) : Lsp) (m + 1) = (Real.sqrt (m + 1) : ℂ) * (x : Lsp) m := rfl

/-- The canonical commutation relation `[a, a†] = 1` on the Fock space. -/
lemma fock_comm (x : FockSub) : annih (creat x) - creat (annih x) = x := by
  apply Subtype.ext; apply lp.ext; funext n
  match n with
  | 0 => simp
  | (m + 1) =>
      simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, annih_apply, creat_apply_succ]
      ring_nf
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Complex.ofReal_pow,
        Real.sq_sqrt (by positivity)]
      push_cast
      ring

/-- `a†` is the adjoint of `a` on the Fock space. -/
lemma fock_adj (x y : FockSub) : ⟪annih x, y⟫_ℂ = ⟪x, creat y⟫_ℂ := by
  show ⟪((annih x : FockSub) : Lsp), (y : Lsp)⟫_ℂ
      = ⟪(x : Lsp), ((creat y : FockSub) : Lsp)⟫_ℂ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    tsum_eq_zero_add' (f := fun n => ⟪((x : Lsp) : ℕ → ℂ) n,
        (((creat y : FockSub) : Lsp) : ℕ → ℂ) n⟫_ℂ)
      ((summable_nat_add_iff 1).2 (lp.summable_inner (x : Lsp) ((creat y : FockSub) : Lsp)))]
  rw [show ⟪((x : Lsp) : ℕ → ℂ) 0, (((creat y : FockSub) : Lsp) : ℕ → ℂ) 0⟫_ℂ = 0 by simp]
  rw [zero_add]
  refine tsum_congr fun n => ?_
  simp only [annih_apply, creat_apply_succ, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- The vacuum vector `e₀`. -/
def vac : FockSub := mkFock (fun n => if n = 0 then 1 else 0) (by
  refine Set.Finite.subset (Set.finite_singleton 0) ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_singleton_iff]
  by_contra hc
  simp [hc] at hn)

lemma vac_ne_zero : vac ≠ 0 := by
  intro h
  have := congrArg (fun v : FockSub => ((v : Lsp) : ℕ → ℂ) 0) h
  simp [vac] at this

lemma annih_vac : annih vac = 0 := by
  apply Subtype.ext; apply lp.ext; funext n
  simp [vac]

/--
**Nonvacuity / concrete instance.**  On the algebraic Fock space, with the standard ladder
operators, the spectrum of `H = ℏω(a†a + ½)` is exactly `{ℏω(n + ½) : n ∈ ℕ}`.
-/
theorem oscillator_spectrum_fock (hbar omega : ℝ) (hhbar : 0 < hbar) (homega : 0 < omega) :
    {z : ℂ | ∃ v : FockSub, v ≠ 0 ∧ hamiltonian hbar omega annih creat v = z • v}
      = {z : ℂ | ∃ n : ℕ, z = ((hbar * omega * (n + 1 / 2) : ℝ) : ℂ)} :=
  oscillator_spectrum annih creat fock_adj fock_comm vac vac_ne_zero annih_vac
    hbar omega hhbar homega


end

end QPhys

#print axioms QPhys.oscillator_spectrum
#print axioms QPhys.oscillator_spectrum_fock

