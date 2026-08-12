/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean 4 requires `import` commands to
-- precede every other command, including module doc-strings.)

import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Spin configurations of a chain of `N` sites (each site carries a qubit). -/
abbrev Config (N : ℕ) := Fin N → Fin 2

/-- Observables of the spin chain: linear operators on the `2^N`-dimensional Hilbert space,
represented as matrices indexed by spin configurations. -/
abbrev SpinOp (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- `Supported S M` says that the observable `M` acts only on the sites in `S`, i.e.
`M = M₀ ⊗ 1` with `M₀` acting on the sites of `S`.  Concretely, matrix elements vanish
unless the configurations agree off `S`, and they depend only on the restrictions to `S`. -/
def Supported {N : ℕ} (S : Set (Fin N)) (M : SpinOp N) : Prop :=
  (∀ c d : Config N, (∃ i, i ∉ S ∧ c i ≠ d i) → M c d = 0) ∧
  (∀ c d c' d' : Config N, (∀ i ∈ S, c i = c' i) → (∀ i ∈ S, d i = d' i) →
    (∀ i, i ∉ S → c i = d i) → (∀ i, i ∉ S → c' i = d' i) → M c d = M c' d')

/-- The one-step neighbourhood of a set of sites in the chain. -/
def nbhd {N : ℕ} (S : Set (Fin N)) : Set (Fin N) := {j | ∃ x ∈ S, |(j : ℤ) - (x : ℤ)| ≤ 1}

/-- `m`-fold neighbourhood. -/
def nbhdIter {N : ℕ} : ℕ → Set (Fin N) → Set (Fin N)
  | 0, S => S
  | (m + 1), S => nbhd (nbhdIter m S)

/-- The commutator with the Hamiltonian: the generator of Heisenberg dynamics. -/
noncomputable def ad {N : ℕ} (H A : SpinOp N) : SpinOp N := H * A - A * H

/-- Iterated commutator `adᴴ ᵐ (A)`; the `m`-th Taylor coefficient of the Heisenberg
evolution is `adPow H m A / m !`. -/
noncomputable def adPow {N : ℕ} (H : SpinOp N) : ℕ → SpinOp N → SpinOp N
  | 0, A => A
  | (m + 1), A => ad H (adPow H m A)

section
variable {N : ℕ}

theorem supported_mono {S T : Set (Fin N)} {M : SpinOp N} (hST : S ⊆ T)
    (hM : Supported S M) : Supported T M := by
  obtain ⟨h0, h1⟩ := hM
  refine ⟨fun c d hne => ?_, fun c d c' d' hcc' hdd' hcd hc'd' => ?_⟩
  · obtain ⟨i, hi, hne⟩ := hne
    exact h0 c d ⟨i, fun hiS => hi (hST hiS), hne⟩
  · by_cases hdiag : ∀ i, i ∉ S → c i = d i
    · refine h1 c d c' d' (fun i hi => hcc' i (hST hi)) (fun i hi => hdd' i (hST hi)) hdiag ?_
      intro i hi
      by_cases hiT : i ∈ T
      · rw [← hcc' i hiT, ← hdd' i hiT]; exact hdiag i hi
      · exact hc'd' i hiT
    · push_neg at hdiag
      obtain ⟨i, hiS, hne⟩ := hdiag
      have hiT : i ∈ T := by
        by_contra hiT
        exact hne (hcd i hiT)
      rw [h0 c d ⟨i, hiS, hne⟩,
        h0 c' d' ⟨i, hiS, by rw [← hcc' i hiT, ← hdd' i hiT]; exact hne⟩]

theorem supported_zero (S : Set (Fin N)) : Supported S (0 : SpinOp N) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem supported_add {S : Set (Fin N)} {M P : SpinOp N} (hM : Supported S M)
    (hP : Supported S P) : Supported S (M + P) := by
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  refine ⟨fun c d hne => ?_, fun c d c' d' h1 h2 h3 h4 => ?_⟩
  · simp [Matrix.add_apply, hM0 c d hne, hP0 c d hne]
  · simp [Matrix.add_apply, hM1 c d c' d' h1 h2 h3 h4, hP1 c d c' d' h1 h2 h3 h4]

theorem supported_sub {S : Set (Fin N)} {M P : SpinOp N} (hM : Supported S M)
    (hP : Supported S P) : Supported S (M - P) := by
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  refine ⟨fun c d hne => ?_, fun c d c' d' h1 h2 h3 h4 => ?_⟩
  · simp [Matrix.sub_apply, hM0 c d hne, hP0 c d hne]
  · simp [Matrix.sub_apply, hM1 c d c' d' h1 h2 h3 h4, hP1 c d c' d' h1 h2 h3 h4]

theorem supported_smul {S : Set (Fin N)} {M : SpinOp N} (t : ℂ) (hM : Supported S M) :
    Supported S (t • M) := by
  obtain ⟨hM0, hM1⟩ := hM
  refine ⟨fun c d hne => ?_, fun c d c' d' h1 h2 h3 h4 => ?_⟩
  · simp [Matrix.smul_apply, hM0 c d hne]
  · simp [Matrix.smul_apply, hM1 c d c' d' h1 h2 h3 h4]

theorem supported_sum {ι : Type*} {S : Set (Fin N)} (s : Finset ι) (f : ι → SpinOp N)
    (hf : ∀ i ∈ s, Supported S (f i)) : Supported S (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using supported_zero S
  | insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact supported_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem swap_eq_right_iff {α : Type*} [DecidableEq α] (a b u : α) :
    Equiv.swap a b u = b ↔ u = a := by
  constructor
  · intro hu
    exact (Equiv.swap a b).injective (hu.trans (Equiv.swap_apply_left a b).symm)
  · rintro rfl
    exact Equiv.swap_apply_left _ _

theorem supported_mul {S T : Set (Fin N)} {M P : SpinOp N} (hM : Supported S M)
    (hP : Supported T P) : Supported (S ∪ T) (M * P) := by
  classical
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  constructor
  · rintro c d ⟨i, hi, hne⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun e _ => ?_)
    by_cases hce : c i = e i
    · have hz : P e d = 0 := hP0 e d ⟨i, fun hiT => hi (Or.inr hiT), by rw [← hce]; exact hne⟩
      rw [hz, mul_zero]
    · have hz : M c e = 0 := hM0 c e ⟨i, fun hiS => hi (Or.inl hiS), hce⟩
      rw [hz, zero_mul]
  · intro c d c' d' hcc' hdd' hcd hc'd'
    rw [Matrix.mul_apply, Matrix.mul_apply]
    set perm : Config N ≃ Config N :=
      Equiv.piCongrRight
        (fun i => if i ∈ S ∪ T then Equiv.refl (Fin 2) else Equiv.swap (c i) (c' i))
    have hperm : ∀ (e : Config N) (i : Fin N),
        perm e i = (if i ∈ S ∪ T then Equiv.refl (Fin 2) else Equiv.swap (c i) (c' i)) (e i) :=
      fun e i => rfl
    have hperm_in : ∀ (e : Config N) (i : Fin N), i ∈ S ∪ T → perm e i = e i := by
      intro e i hi
      rw [hperm e i, if_pos hi]
      rfl
    have hperm_out : ∀ (e : Config N) (i : Fin N), i ∉ S ∪ T →
        perm e i = Equiv.swap (c i) (c' i) (e i) := by
      intro e i hi
      rw [hperm e i, if_neg hi]
    refine Fintype.sum_equiv perm _ _ (fun e => ?_)
    -- pointwise transfer of the two "diagonal" conditions
    have hA_iff : ∀ i, i ∉ S → (c i = e i ↔ c' i = perm e i) := by
      intro i hi
      by_cases hiT : i ∈ T
      · rw [hperm_in e i (Or.inr hiT), hcc' i (Or.inr hiT)]
      · have hiST : i ∉ S ∪ T := fun hmem => hmem.elim hi hiT
        rw [hperm_out e i hiST]
        constructor
        · intro hce; rw [← hce, Equiv.swap_apply_left]
        · intro hce; exact ((swap_eq_right_iff (c i) (c' i) (e i)).mp hce.symm).symm
    have hB_iff : ∀ i, i ∉ T → (e i = d i ↔ perm e i = d' i) := by
      intro i hi
      by_cases hiS : i ∈ S
      · rw [hperm_in e i (Or.inl hiS), hdd' i (Or.inl hiS)]
      · have hiST : i ∉ S ∪ T := fun hmem => hmem.elim hiS hi
        rw [hperm_out e i hiST, ← hc'd' i hiST, ← hcd i hiST]
        exact (swap_eq_right_iff (c i) (c' i) (e i)).symm
    by_cases hda : ∀ i, i ∉ S → c i = e i
    · by_cases hdb : ∀ i, i ∉ T → e i = d i
      · have h1 : M c e = M c' (perm e) :=
          hM1 c e c' (perm e) (fun i hi => hcc' i (Or.inl hi))
            (fun i hi => (hperm_in e i (Or.inl hi)).symm) hda
            (fun i hi => (hA_iff i hi).mp (hda i hi))
        have h2 : P e d = P (perm e) d' :=
          hP1 e d (perm e) d' (fun i hi => (hperm_in e i (Or.inr hi)).symm)
            (fun i hi => hdd' i (Or.inr hi)) hdb
            (fun i hi => (hB_iff i hi).mp (hdb i hi))
        rw [h1, h2]
      · push_neg at hdb
        obtain ⟨i, hi, hne⟩ := hdb
        have hz1 : P e d = 0 := hP0 e d ⟨i, hi, hne⟩
        have hz2 : P (perm e) d' = 0 :=
          hP0 (perm e) d' ⟨i, hi, fun hcon => hne ((hB_iff i hi).mpr hcon)⟩
        rw [hz1, hz2, mul_zero, mul_zero]
    · push_neg at hda
      obtain ⟨i, hi, hne⟩ := hda
      have hz1 : M c e = 0 := hM0 c e ⟨i, hi, hne⟩
      have hz2 : M c' (perm e) = 0 :=
        hM0 c' (perm e) ⟨i, hi, fun hcon => hne ((hA_iff i hi).mpr hcon)⟩
      rw [hz1, hz2, zero_mul, zero_mul]

/-- Observables supported on disjoint sets of sites commute. -/
theorem commute_of_disjoint {S T : Set (Fin N)} {M P : SpinOp N} (hST : Disjoint S T)
    (hM : Supported S M) (hP : Supported T P) : M * P = P * M := by
  classical
  have hMP := supported_mul hM hP
  have hPM := supported_mul hP hM
  obtain ⟨hM0, hM1⟩ := hM
  obtain ⟨hP0, hP1⟩ := hP
  ext c d
  by_cases hcd : ∀ i, i ∉ S ∪ T → c i = d i
  · -- both matrix elements reduce to a single term of the sum
    set e1 : Config N := fun i => if i ∈ S then d i else c i with he1
    set e2 : Config N := fun i => if i ∈ T then d i else c i with he2
    have hSnotT : ∀ i, i ∈ S → i ∉ T := fun i hi => Set.disjoint_left.mp hST hi
    have hTnotS : ∀ i, i ∈ T → i ∉ S := fun i hi => Set.disjoint_right.mp hST hi
    have hleft : (M * P) c d = M c e1 * P e1 d := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single e1 (fun e _ hne => ?_) (fun hcon => absurd (Finset.mem_univ e1) hcon)
      by_contra hprod
      have h1 : ∀ i, i ∉ S → c i = e i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hM0 c e ⟨i, hi, hci⟩, zero_mul])
      have h2 : ∀ i, i ∉ T → e i = d i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hP0 e d ⟨i, hi, hci⟩, mul_zero])
      refine hne (funext fun i => ?_)
      by_cases hiS : i ∈ S
      · rw [he1]; simp only [if_pos hiS]; exact h2 i (hSnotT i hiS)
      · rw [he1]; simp only [if_neg hiS]; exact (h1 i hiS).symm
    have hright : (P * M) c d = P c e2 * M e2 d := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single e2 (fun e _ hne => ?_) (fun hcon => absurd (Finset.mem_univ e2) hcon)
      by_contra hprod
      have h1 : ∀ i, i ∉ T → c i = e i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hP0 c e ⟨i, hi, hci⟩, zero_mul])
      have h2 : ∀ i, i ∉ S → e i = d i := by
        intro i hi
        by_contra hci
        exact hprod (by rw [hM0 e d ⟨i, hi, hci⟩, mul_zero])
      refine hne (funext fun i => ?_)
      by_cases hiT : i ∈ T
      · rw [he2]; simp only [if_pos hiT]; exact h2 i (hTnotS i hiT)
      · rw [he2]; simp only [if_neg hiT]; exact (h1 i hiT).symm
    have hMeq : M c e1 = M e2 d := by
      refine hM1 c e1 e2 d (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
      · rw [he2]; simp only [if_neg (hSnotT i hi)]
      · rw [he1]; simp only [if_pos hi]
      · rw [he1]; simp only [if_neg hi]
      · rw [he2]
        by_cases hiT : i ∈ T
        · simp only [if_pos hiT]
        · simp only [if_neg hiT]
          exact hcd i (fun hmem => hmem.elim hi hiT)
    have hPeq : P e1 d = P c e2 := by
      refine hP1 e1 d c e2 (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
      · rw [he1]; simp only [if_neg (hTnotS i hi)]
      · rw [he2]; simp only [if_pos hi]
      · rw [he1]
        by_cases hiS : i ∈ S
        · simp only [if_pos hiS]
        · simp only [if_neg hiS]
          exact hcd i (fun hmem => hmem.elim hiS hi)
      · rw [he2]; simp only [if_neg hi]
    rw [hleft, hright, hMeq, hPeq, mul_comm]
  · push_neg at hcd
    obtain ⟨i, hi, hne⟩ := hcd
    have hi' : i ∉ T ∪ S := fun hmem => hi hmem.symm
    rw [hMP.1 c d ⟨i, hi, hne⟩, hPM.1 c d ⟨i, hi', hne⟩]

end

section
variable {N : ℕ} {ι : Type*}

theorem subset_nbhd {N : ℕ} (S : Set (Fin N)) : S ⊆ nbhd S :=
  fun x hx => ⟨x, hx, by simp⟩

/-- One step of the Heisenberg generator enlarges the support by at most one site. -/
theorem supported_ad {S : Set (Fin N)} {A : SpinOp N} (s : Finset ι) (h : ι → SpinOp N)
    (X : ι → Set (Fin N)) (hloc : ∀ i ∈ s, Supported (X i) (h i))
    (hdiam : ∀ i ∈ s, ∀ a ∈ X i, ∀ b ∈ X i, |(a : ℤ) - (b : ℤ)| ≤ 1)
    (hA : Supported S A) : Supported (nbhd S) (ad (∑ i ∈ s, h i) A) := by
  have hexp : ad (∑ i ∈ s, h i) A = ∑ i ∈ s, (h i * A - A * h i) := by
    rw [ad, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hexp]
  refine supported_sum s _ (fun i hi => ?_)
  by_cases hdis : Disjoint (X i) S
  · have hcomm := commute_of_disjoint hdis (hloc i hi) hA
    rw [hcomm, sub_self]
    exact supported_zero _
  · rw [Set.not_disjoint_iff] at hdis
    obtain ⟨z, hzX, hzS⟩ := hdis
    have hsub : X i ∪ S ⊆ nbhd S := by
      rintro j (hj | hj)
      · exact ⟨z, hzS, hdiam i hi j hj z hzX⟩
      · exact subset_nbhd S hj
    have hsub' : S ∪ X i ⊆ nbhd S := by rw [Set.union_comm]; exact hsub
    exact supported_sub (supported_mono hsub (supported_mul (hloc i hi) hA))
      (supported_mono hsub' (supported_mul hA (hloc i hi)))

/-- After `m` steps of the Heisenberg generator the support has grown by at most `m` sites. -/
theorem supported_adPow {S : Set (Fin N)} {A : SpinOp N} (s : Finset ι) (h : ι → SpinOp N)
    (X : ι → Set (Fin N)) (hloc : ∀ i ∈ s, Supported (X i) (h i))
    (hdiam : ∀ i ∈ s, ∀ a ∈ X i, ∀ b ∈ X i, |(a : ℤ) - (b : ℤ)| ≤ 1)
    (hA : Supported S A) (m : ℕ) :
    Supported (nbhdIter m S) (adPow (∑ i ∈ s, h i) m A) := by
  induction m with
  | zero => exact hA
  | succ m ih => exact supported_ad s h X hloc hdiam ih

theorem nbhdIter_singleton_subset {N : ℕ} (x : Fin N) (m : ℕ) :
    nbhdIter m ({x} : Set (Fin N)) ⊆ {j | |(j : ℤ) - (x : ℤ)| ≤ m} := by
  induction m with
  | zero =>
    intro j hj
    simp only [nbhdIter, Set.mem_singleton_iff] at hj
    subst hj
    simp
  | succ m ih =>
    intro j hj
    simp only [nbhdIter, nbhd, Set.mem_setOf_eq] at hj
    obtain ⟨z, hz, hjz⟩ := hj
    have h1 : |(z : ℤ) - (x : ℤ)| ≤ (m : ℤ) := ih hz
    have h2 : |(j : ℤ) - (x : ℤ)| ≤ |(j : ℤ) - (z : ℤ)| + |(z : ℤ) - (x : ℤ)| := abs_sub_le _ _ _
    simp only [Set.mem_setOf_eq]
    push_cast
    linarith

end

/-- **Lieb–Robinson bound (strict light cone for a nearest-neighbour spin chain).**

Let `H = ∑ i ∈ s, h i` be a Hamiltonian on a chain of `N` qubits which is a sum of
interaction terms `h i`, each supported on a set `X i` of sites of diameter at most `1`
(nearest-neighbour interactions).  Let `A` be an observable at site `x` and `B` an
observable at site `y`.  Then every Taylor truncation, to order `K < |x - y|`, of the
Heisenberg evolution `τ_t(A) = ∑ₘ (tᵐ/m!) adᴴ ᵐ (A)` of `A` commutes *exactly* with `B`.

This is the base case of the Lieb–Robinson bound: information cannot leave the light cone
`|x - y| ≤ (order in t)`; all contributions to `[τ_t(A), B]` come from orders at least
`|x - y|`, whose size is controlled by `(2‖H‖|t|)^{|x-y|}/|x-y|!`. -/
theorem lieb_robinson {N : ℕ} {ι : Type*} (s : Finset ι) (h : ι → SpinOp N)
    (X : ι → Set (Fin N)) (hloc : ∀ i ∈ s, Supported (X i) (h i))
    (hdiam : ∀ i ∈ s, ∀ a ∈ X i, ∀ b ∈ X i, |(a : ℤ) - (b : ℤ)| ≤ 1)
    (A B : SpinOp N) (x y : Fin N) (hA : Supported {x} A) (hB : Supported {y} B)
    (K : ℕ) (hK : (K : ℤ) < |(x : ℤ) - (y : ℤ)|) (t : ℂ) :
    Commute (∑ m ∈ Finset.range (K + 1), (t ^ m / (m ! : ℂ)) • adPow (∑ i ∈ s, h i) m A) B := by
  have hball : ∀ m ∈ Finset.range (K + 1),
      Supported {j : Fin N | |(j : ℤ) - (x : ℤ)| ≤ (K : ℤ)}
        ((t ^ m / (m ! : ℂ)) • adPow (∑ i ∈ s, h i) m A) := by
    intro m hm
    have hmK : (m : ℤ) ≤ (K : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    refine supported_smul _ (supported_mono ?_ (supported_adPow s h X hloc hdiam hA m))
    intro j hj
    have hjm := nbhdIter_singleton_subset x m hj
    simp only [Set.mem_setOf_eq] at hjm ⊢
    linarith
  have hsum := supported_sum (Finset.range (K + 1)) _ hball
  have hdisj : Disjoint {j : Fin N | |(j : ℤ) - (x : ℤ)| ≤ (K : ℤ)} ({y} : Set (Fin N)) := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_setOf_eq]
    intro hy
    rw [abs_sub_comm] at hK
    linarith
  exact commute_of_disjoint hdisj hsum hB

/-!
## Non-vacuity

The hypotheses of `lieb_robinson` are satisfied by a genuine nearest-neighbour spin chain:
the Pauli `X` operators are nonzero observables supported on a single site, and the
`XX`-chain Hamiltonian `∑ ⟨p,q⟩ nearest neighbours, X_p X_q` is a sum of terms supported on
sets of sites of diameter at most one.
-/

/-- The Pauli `X` operator at site `k` (spin flip at `k`, identity elsewhere). -/
noncomputable def pauliX {N : ℕ} (k : Fin N) : SpinOp N :=
  Matrix.of fun c d => if (∀ i, i ≠ k → c i = d i) ∧ c k ≠ d k then (1 : ℂ) else 0

theorem supported_pauliX {N : ℕ} (k : Fin N) : Supported ({k} : Set (Fin N)) (pauliX k) := by
  constructor
  · rintro c d ⟨i, hi, hne⟩
    simp only [pauliX, Matrix.of_apply]
    rw [if_neg]
    rintro ⟨hagree, -⟩
    exact hne (hagree i (by simpa using hi))
  · intro c d c' d' hcc' hdd' hcd hc'd'
    have hck : c k = c' k := hcc' k rfl
    have hdk : d k = d' k := hdd' k rfl
    have hagree : ∀ i, i ≠ k → c i = d i := fun i hi => hcd i (by simpa using hi)
    have hagree' : ∀ i, i ≠ k → c' i = d' i := fun i hi => hc'd' i (by simpa using hi)
    have hiff : ((∀ i, i ≠ k → c i = d i) ∧ c k ≠ d k) ↔
        ((∀ i, i ≠ k → c' i = d' i) ∧ c' k ≠ d' k) :=
      ⟨fun hh => ⟨hagree', by rw [← hck, ← hdk]; exact hh.2⟩,
       fun hh => ⟨hagree, by rw [hck, hdk]; exact hh.2⟩⟩
    simp only [pauliX, Matrix.of_apply]
    exact if_congr hiff rfl rfl

theorem pauliX_ne_zero {N : ℕ} (k : Fin N) : pauliX k ≠ 0 := by
  intro hcon
  have h := congrFun (congrFun hcon (fun _ => 0)) (fun i => if i = k then 1 else 0)
  simp only [pauliX, Matrix.of_apply, Matrix.zero_apply, if_pos] at h
  rw [if_pos] at h
  · exact one_ne_zero h
  · exact ⟨fun i hi => by simp [hi], by simp⟩

/-- The set of nearest-neighbour pairs of sites of the chain. -/
def nnPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p : Fin N × Fin N => |(p.1 : ℤ) - (p.2 : ℤ)| ≤ 1)

/-- **Lieb–Robinson light cone for the `XX` chain.**  A concrete instance of
`lieb_robinson`, showing that its hypotheses are not vacuous. -/
theorem lieb_robinson_XX {N : ℕ} (x y : Fin N) (K : ℕ)
    (hK : (K : ℤ) < |(x : ℤ) - (y : ℤ)|) (t : ℂ) :
    Commute (∑ m ∈ Finset.range (K + 1), (t ^ m / (m ! : ℂ)) •
      adPow (∑ p ∈ nnPairs N, pauliX p.1 * pauliX p.2) m (pauliX x)) (pauliX y) := by
  refine lieb_robinson (nnPairs N) _ (fun p => {p.1, p.2}) (fun p _ => ?_)
    (fun p hp a ha b hb => ?_) _ _ x y (supported_pauliX x) (supported_pauliX y) K hK t
  · have hmul := supported_mul (supported_pauliX p.1) (supported_pauliX p.2)
    rwa [Set.singleton_union] at hmul
  · have hp12 : |(p.1 : ℤ) - (p.2 : ℤ)| ≤ 1 := (Finset.mem_filter.mp hp).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first
      | exact hp12
      | (rw [abs_sub_comm]; exact hp12)
      | simp

end Frontier

