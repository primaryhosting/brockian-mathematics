import Mathlib
import RequestProject.Circuit

/-!
A non-triviality check for the circuit model: the class `AC⁰[q]` really does contain the
`MOD q` function, computed by the depth-one circuit consisting of a single `MOD q` gate
applied to all inputs.  This guards against the main theorem being vacuously true because
the circuit model computes nothing.
-/

namespace CS

open Finset

theorem list_length_filter_eq_sum {α : Type*} (l : List α) (w : α → Bool) :
    (l.filter w).length = (l.map (fun a => if w a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases h : w a <;> simp [h, ih, add_comm]

theorem foldr_max_eq_zero : ∀ l : List ℕ, (∀ a ∈ l, a = 0) → l.foldr max 0 = 0
  | [], _ => rfl
  | a :: l, h => by
      rw [List.foldr_cons, h a (by simp), foldr_max_eq_zero l (fun b hb => h b (by simp [hb]))]
      rfl

/-- The circuit consisting of a single `MOD q` gate applied to all `n` inputs. -/
def modCircuit (n : ℕ) : Circuit n where
  size := n + 1
  gate := fun i => if h : i.val < n then .inp ⟨i.val, h⟩ else .modg (List.finRange i.val)
  out := ⟨n, Nat.lt_succ_self n⟩

theorem modCircuit_gate_out (n : ℕ) :
    (modCircuit n).gate (modCircuit n).out = .modg (List.finRange n) := by
  simp only [modCircuit]
  rw [dif_neg (lt_irrefl n)]

theorem modCircuit_gval_inp (q n : ℕ) (x : Fin n → Bool) (i : Fin (modCircuit n).size)
    (h : i.val < n) : (modCircuit n).gval q x i = x ⟨i.val, h⟩ := by
  rw [Circuit.gval]
  simp only [modCircuit, dif_pos h]

theorem modCircuit_gdepth_inp (n : ℕ) (i : Fin (modCircuit n).size) (h : i.val < n) :
    (modCircuit n).gdepth i = 0 := by
  rw [Circuit.gdepth]
  simp only [modCircuit, dif_pos h]

theorem modCircuit_eval (q n : ℕ) (x : Fin n → Bool) :
    (modCircuit n).eval q x = ModFun q n x := by
  rw [Circuit.eval, Circuit.gval, modCircuit_gate_out]
  simp only []
  have hfil : (List.filter
        (fun j => (modCircuit n).gval q x ((modCircuit n).up (modCircuit n).out j))
        (List.finRange n))
      = List.filter (fun j : Fin n => x j) (List.finRange n) := by
    refine List.filter_congr ?_
    intro j _
    exact modCircuit_gval_inp q n x ((modCircuit n).up (modCircuit n).out j) j.isLt
  rw [hfil, list_length_filter_eq_sum]
  simp only [ModFun, popc, Fin.sum_univ_def]
  rfl

theorem modCircuit_depth (n : ℕ) : (modCircuit n).depth = 1 := by
  rw [Circuit.depth, Circuit.gdepth, modCircuit_gate_out]
  simp only []
  rw [foldr_max_eq_zero _ ?_]
  intro a ha
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
  exact modCircuit_gdepth_inp n _ j.isLt

/-- Non-triviality check: the class `AC⁰[q]` contains the `MOD q` function. -/
theorem modFun_self_mem_AC0mod (q : ℕ) : InAC0mod q (ModFun q) := by
  refine ⟨1, 1, 1, fun n => ⟨modCircuit n, ?_, ?_, fun x => modCircuit_eval q n x⟩⟩
  · simp [modCircuit]
  · rw [modCircuit_depth]

end CS

import Mathlib

/-!
Counting lemmas used in the proof of Razborov's approximation lemma.

The main statement is `CS.card_gate_bad_le`: if a nonempty set `S` of children of a gate
carries a "witness" `j₀` with `w j₀ = true`, then the set of random choices `ρ` for which
*every* one of the `t` random restrictions at that gate selects a multiple of `q` many
witnesses has density at most `2^{-t}`.
-/

namespace CS

open Finset
open scoped Classical

/-- Counting functions `ι → β` by the value at a single coordinate. -/
theorem card_filter_coord {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (i : ι) (Q : β → Prop) :
    (univ.filter (fun ρ : ι → β => Q (ρ i))).card * Fintype.card β
      = (univ.filter Q).card * Fintype.card (ι → β) := by
  have hset : (univ.filter (fun ρ : ι → β => Q (ρ i)))
      = Fintype.piFinset (fun i' => if i' = i then univ.filter Q else univ) := by
    ext ρ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i'
      by_cases hi : i' = i
      · subst hi; simpa using h
      · simp [hi]
    · intro h
      simpa using h i
  rw [hset, Fintype.card_piFinset]
  have h1 : ∏ i' : ι, (if i' = i then univ.filter Q else univ).card
      = (univ.filter Q).card * ∏ _i' ∈ univ.erase i, (Fintype.card β) := by
    rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
    simp only
    congr 1
    refine Finset.prod_congr rfl (fun i' hi' => ?_)
    rw [if_neg (Finset.mem_erase.1 hi').1]
    simp
  rw [h1]
  have h2 : Fintype.card (ι → β) = Fintype.card β * ∏ _i' ∈ univ.erase i, (Fintype.card β) := by
    simp only [Finset.prod_const, Fintype.card_fun]
    rw [Finset.card_erase_of_mem (mem_univ i)]
    have h3 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [← pow_succ']
    congr 1
    simp only [Finset.card_univ]
    omega
  rw [h2]
  ring

/-- If a property of a single coordinate has density at most `2^{-t}`, then so does the set of
functions whose value at a fixed coordinate has the property. -/
theorem card_coord_bad_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
    [Nonempty β] (i : ι) (Q : β → Prop) (t : ℕ)
    (hQ : (univ.filter Q).card * 2 ^ t ≤ Fintype.card β)
    (Bad : Finset (ι → β)) (hsub : Bad ⊆ univ.filter (fun ρ => Q (ρ i))) :
    Bad.card * 2 ^ t ≤ Fintype.card (ι → β) := by
  have hcb : 0 < Fintype.card β := Fintype.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hcb
  calc Bad.card * 2 ^ t * Fintype.card β
      = Bad.card * Fintype.card β * 2 ^ t := by ring
    _ ≤ (univ.filter (fun ρ : ι → β => Q (ρ i))).card * Fintype.card β * 2 ^ t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Finset.card_le_card hsub))
    _ = ((univ.filter Q).card * 2 ^ t) * Fintype.card (ι → β) := by
        rw [card_filter_coord i Q]; ring
    _ ≤ Fintype.card β * Fintype.card (ι → β) := Nat.mul_le_mul_right _ hQ
    _ = Fintype.card (ι → β) * Fintype.card β := by ring

/-- At most half of the random subsets select a multiple of `q` many witnesses, provided at
least one witness exists.  Proved by the involution flipping the coordinate `up j₀`. -/
theorem card_dvd_le {m k q : ℕ} (hq : 2 ≤ q) (S : Finset (Fin k)) (up : Fin k → Fin m)
    (hup : Function.Injective up) (w : Fin k → Bool) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (hw : w j₀ = true) :
    2 * (univ.filter (fun r : Fin m → Bool =>
        q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card)).card ≤ 2 ^ m := by
  set a := up j₀ with ha
  set flip : (Fin m → Bool) → (Fin m → Bool) :=
    fun r => fun c => if c = a then !(r c) else r c with hflip
  have hinv : Function.Involutive flip := by
    intro r; funext c; by_cases h : c = a <;> simp [hflip, h]
  set A := univ.filter (fun r : Fin m → Bool =>
      q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card) with hA
  have hkey : ∀ r : Fin m → Bool, ¬ (r ∈ A ∧ flip r ∈ A) := by
    rintro r ⟨h1, h2⟩
    simp only [hA, mem_filter, mem_univ, true_and] at h1 h2
    set T := S.filter (fun j => r (up j) = true ∧ w j = true) with hT
    set T' := S.filter (fun j => flip r (up j) = true ∧ w j = true) with hT'
    have hne : ∀ j : Fin k, j ≠ j₀ → flip r (up j) = r (up j) := by
      intro j hj
      have hja : up j ≠ a := fun hc => hj (hup hc)
      simp [hflip, hja]
    by_cases hb : r a = true
    · have hj₀T : j₀ ∈ T := by simp [hT, hj₀, hw, ← ha, hb]
      have hTT : T' = T.erase j₀ := by
        ext j
        simp only [hT, hT', mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hjS, hjr, hjw⟩
          have hj : j ≠ j₀ := by
            rintro rfl; rw [← ha] at hjr; simp [hflip, hb] at hjr
          exact ⟨hj, hjS, by rwa [hne j hj] at hjr, hjw⟩
        · rintro ⟨hj, hjS, hjr, hjw⟩
          exact ⟨hjS, by rwa [hne j hj], hjw⟩
      rw [hTT, Finset.card_erase_of_mem hj₀T] at h2
      have hc1 : 1 ≤ T.card := Finset.card_pos.2 ⟨j₀, hj₀T⟩
      have hd : q ∣ 1 := by
        have := Nat.dvd_sub h1 h2
        simpa [Nat.sub_sub_self hc1] using this
      have := Nat.le_of_dvd one_pos hd
      omega
    · have hb' : r a = false := by simpa using hb
      have hj₀T : j₀ ∉ T := by simp [hT, ← ha, hb']
      have hTT : T' = insert j₀ T := by
        ext j
        simp only [hT, hT', mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hjS, hjr, hjw⟩
          by_cases hj : j = j₀
          · exact Or.inl hj
          · exact Or.inr ⟨hjS, by rwa [hne j hj] at hjr, hjw⟩
        · rintro (rfl | ⟨hjS, hjr, hjw⟩)
          · exact ⟨hj₀, by rw [← ha]; simp [hflip, hb'], hw⟩
          · by_cases hj : j = j₀
            · subst hj; exact ⟨hjS, by rw [← ha]; simp [hflip, hb'], hjw⟩
            · exact ⟨hjS, by rwa [hne j hj], hjw⟩
      rw [hTT, Finset.card_insert_of_notMem hj₀T] at h2
      have hd : q ∣ 1 := by simpa using Nat.dvd_sub h2 h1
      have := Nat.le_of_dvd one_pos hd
      omega
  have hdisj : Disjoint A (A.image flip) := by
    rw [Finset.disjoint_right]
    rintro r hr hrA
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
    exact hkey s ⟨hs, hrA⟩
  have hcard : (A.image flip).card = A.card :=
    Finset.card_image_of_injective _ hinv.injective
  have hle : A.card + (A.image flip).card ≤ Fintype.card (Fin m → Bool) := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  rw [hcard] at hle
  simpa [Fintype.card_fun, two_mul] using hle

/-- The density of the set of randomness for which a single gate fails is at most `2^{-t}`. -/
theorem card_gate_bad_le {m k q t : ℕ} (hq : 2 ≤ q) (S : Finset (Fin k)) (up : Fin k → Fin m)
    (hup : Function.Injective up) (w : Fin k → Bool) (j₀ : Fin k) (hj₀ : j₀ ∈ S)
    (hw : w j₀ = true) (i : Fin m) (Bad : Finset (Fin m → Fin t → Fin m → Bool))
    (hsub : ∀ ρ ∈ Bad, ∀ κ : Fin t,
      q ∣ (S.filter (fun j => ρ i κ (up j) = true ∧ w j = true)).card) :
    Bad.card * 2 ^ t ≤ Fintype.card (Fin m → Fin t → Fin m → Bool) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin t → Fin m → Bool) → Prop, ∀ b, Q b ↔
      (∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hbridge : (univ.filter Q) = univ.filter (fun b : Fin t → Fin m → Bool =>
      ∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card) := by
    ext b; simp [hQ]
  have hQcard : (univ.filter Q).card * 2 ^ t ≤ Fintype.card (Fin t → Fin m → Bool) := by
    rw [hbridge]
    have hset : (univ.filter (fun b : Fin t → Fin m → Bool =>
        ∀ κ : Fin t, q ∣ (S.filter (fun j => b κ (up j) = true ∧ w j = true)).card))
        = Fintype.piFinset (fun _ : Fin t => univ.filter (fun r : Fin m → Bool =>
            q ∣ (S.filter (fun j => r (up j) = true ∧ w j = true)).card)) := by
      ext b; simp [Fintype.mem_piFinset]
    rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_pow]
    have h2 : Fintype.card (Fin t → Fin m → Bool) = (2 ^ m) ^ t := by simp
    rw [h2]
    exact Nat.pow_le_pow_left (by have := card_dvd_le hq S up hup w j₀ hj₀ hw; omega) t
  refine card_coord_bad_le i Q t hQcard Bad ?_
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hQ _).2 (hsub ρ hρ)

end CS

import Mathlib
import RequestProject.Poly
import RequestProject.Circuit

/-!
The Smolensky counting argument: if the function `x ↦ ζ^(popcount x)` (for `ζ` a root of
unity) agrees on a set `A ⊆ {0,1}ⁿ`, `n = 2m+1`, with a function of degree at most `D`,
then `|A| ≤ ∑_{i ≤ m + D} C(n,i)`.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `x ↦ ζ ^ (x i)`. -/
def yfun (ζ : F) (i : Fin n) : (Fin n → Bool) → F := fun x => if x i then ζ else 1

/-- `x ↦ ∏_{i ∈ S} ζ ^ (x i)`. -/
def ymono (ζ : F) (S : Finset (Fin n)) : (Fin n → Bool) → F := ∏ i ∈ S, yfun ζ i

theorem yfun_mem_Deg (ζ : F) (i : Fin n) : yfun ζ i ∈ Deg F n 1 := by
  have : yfun ζ i = (fun _ => (1 : F)) + (ζ - 1) • mono F {i} := by
    funext x
    simp only [yfun, mono_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : x i = true <;> simp [h]
  rw [this]
  exact Submodule.add_mem _ (Deg_const_mem 1) (Submodule.smul_mem _ _ (mono_mem_Deg (by simp)))

theorem ymono_mem_Deg (ζ : F) (S : Finset (Fin n)) : ymono ζ S ∈ Deg F n S.card := by
  have := Deg_prod (F := F) (s := S) (f := fun i => yfun ζ i) (e := 1)
    (fun i _ => yfun_mem_Deg ζ i)
  simpa [ymono] using this

theorem ymono_apply_univ (ζ : F) (x : Fin n → Bool) :
    ymono ζ (univ : Finset (Fin n)) x = ζ ^ (popc x) := by
  simp only [ymono, Finset.prod_apply, popc, yfun]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases h : x i <;> simp

theorem ymono_mul_inv (ζ : F) (hζ : ζ ≠ 0) (S : Finset (Fin n)) (x : Fin n → Bool) :
    ymono ζ (univ : Finset (Fin n)) x * ymono ζ⁻¹ (univ \ S) x = ymono ζ S x := by
  have h1 : ymono ζ (univ : Finset (Fin n)) = ymono ζ (univ \ S) * ymono ζ S := by
    rw [ymono, ymono, ymono, Finset.prod_sdiff (Finset.subset_univ S)]
  rw [h1]
  simp only [Pi.mul_apply]
  have h2 : ymono ζ (univ \ S) x * ymono ζ⁻¹ (univ \ S) x = 1 := by
    simp only [ymono, Finset.prod_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun i _ => ?_)
    simp only [yfun]
    cases h : x i <;> simp [hζ]
  calc ymono ζ (univ \ S) x * ymono ζ S x * ymono ζ⁻¹ (univ \ S) x
      = (ymono ζ (univ \ S) x * ymono ζ⁻¹ (univ \ S) x) * ymono ζ S x := by ring
    _ = ymono ζ S x := by rw [h2, one_mul]

/-- The submodule of functions that agree on `A` with a function of degree at most `d`. -/
def AgreeDeg (F : Type*) [Field F] {n : ℕ} (A : Finset (Fin n → Bool)) (d : ℕ) :
    Submodule F ((Fin n → Bool) → F) where
  carrier := {f | ∃ g ∈ Deg F n d, ∀ x ∈ A, g x = f x}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, fun x hx => by
      simp [Pi.add_apply, h₁ x hx, h₂ x hx]⟩
  zero_mem' := ⟨0, Submodule.zero_mem _, fun x _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨g, hg, h⟩
    exact ⟨c • g, Submodule.smul_mem _ _ hg, fun x hx => by
      simp [Pi.smul_apply, h x hx]⟩

theorem mem_AgreeDeg_of_mem_Deg {A : Finset (Fin n → Bool)} {d : ℕ}
    {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n d) : f ∈ AgreeDeg F A d :=
  ⟨f, hf, fun _ _ => rfl⟩

/-- The key step: on `A`, every `y`-monomial has degree at most `m + D`. -/
theorem ymono_mem_AgreeDeg {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (h : (Fin (2 * m + 1) → Bool) → F) (hhD : h ∈ Deg F (2 * m + 1) D)
    (hh : ∀ x ∈ A, h x = ymono ζ univ x) (S : Finset (Fin (2 * m + 1))) :
    ymono ζ S ∈ AgreeDeg F A (m + D) := by
  by_cases hS : S.card ≤ m
  · exact mem_AgreeDeg_of_mem_Deg (mem_Deg_of_le (ymono_mem_Deg ζ S) (by omega))
  · push_neg at hS
    refine ⟨h * ymono ζ⁻¹ (univ \ S), ?_, ?_⟩
    · have hcard : (univ \ S).card ≤ m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simp only [Finset.card_univ, Fintype.card_fin]
        omega
      exact mem_Deg_of_le (Deg_mul hhD (mem_Deg_of_le (ymono_mem_Deg ζ⁻¹ (univ \ S)) hcard))
        (by omega)
    · intro x hx
      rw [Pi.mul_apply, hh x hx, ymono_mul_inv ζ hζ0]

/-- Hence every function agrees on `A` with a function of degree at most `m + D`. -/
theorem AgreeDeg_eq_top {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (h : (Fin (2 * m + 1) → Bool) → F)
    (hhD : h ∈ Deg F (2 * m + 1) D) (hh : ∀ x ∈ A, h x = ymono ζ univ x) :
    AgreeDeg F A (m + D) = ⊤ := by
  have hne : (ζ - 1) ≠ 0 := sub_ne_zero.2 hζ1
  rw [eq_top_iff, ← Deg_top (F := F) (n := 2 * m + 1), Deg, Submodule.span_le]
  rintro f ⟨S, -, rfl⟩
  have hexp : (∏ i ∈ S, (yfun ζ i + (fun _ => (-1 : F))))
      = ∑ T ∈ S.powerset, (ymono ζ T) * (∏ _i ∈ S \ T, (fun _ => (-1 : F))) := by
    rw [Finset.prod_add]
    rfl
  have hmono : mono F S = ((ζ - 1)⁻¹) ^ S.card • (∏ i ∈ S, (yfun ζ i + (fun _ => (-1 : F)))) := by
    funext x
    simp only [Finset.prod_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have hpt : ∀ i ∈ S, (yfun ζ i x + (-1 : F)) = (ζ - 1) * (if x i then (1 : F) else 0) := by
      intro i _
      simp only [yfun]
      cases hx : x i <;> simp; ring
    rw [Finset.prod_congr rfl hpt, Finset.prod_mul_distrib, Finset.prod_const,
      ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hne, one_pow, one_mul]
    rfl
  rw [SetLike.mem_coe, hmono]
  refine Submodule.smul_mem _ _ ?_
  rw [hexp]
  refine Submodule.sum_mem _ (fun T _ => ?_)
  have h1 : (ymono ζ T) * (∏ _i ∈ S \ T, (fun _ => (-1 : F)))
      = ((-1 : F)) ^ (S \ T).card • (ymono ζ T) := by
    funext x
    simp [Finset.prod_const, mul_comm]
  rw [h1]
  exact Submodule.smul_mem _ _ (ymono_mem_AgreeDeg ζ hζ0 h hhD hh T)

/-- Smolensky's counting bound. -/
theorem smolensky_counting {m D : ℕ} {A : Finset (Fin (2 * m + 1) → Bool)} (ζ : F)
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (h : (Fin (2 * m + 1) → Bool) → F)
    (hhD : h ∈ Deg F (2 * m + 1) D) (hh : ∀ x ∈ A, h x = ymono ζ univ x) :
    A.card ≤ ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i := by
  refine card_le_of_agree F A (fun f => ?_)
  have htop := AgreeDeg_eq_top ζ hζ0 hζ1 h hhD hh
  have hf : f ∈ AgreeDeg F A (m + D) := by rw [htop]; trivial
  exact hf

end CS

import Mathlib

/-!
Elementary binomial coefficient estimates: the central binomial coefficient is at most
`√2 · 4ⁿ / √(n+1)`, in the division free form `(n.choose i)^2 * (n+1) ≤ 2 * 4^n`.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 (3m+1) ≤ 16^m`, proved by induction. -/
theorem centralBinom_sq_le (m : ℕ) : (Nat.centralBinom m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have key : (m + 1) * Nat.centralBinom (m + 1) = 2 * (2 * m + 1) * Nat.centralBinom m :=
        Nat.succ_mul_centralBinom_succ m
      have h2 : ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1)
          = 4 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 * (3 * m + 4) := by
        rw [key]; ring
      have h3 : 4 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 * (3 * m + 4) * (3 * m + 1)
          ≤ 16 ^ (m + 1) * (m + 1) ^ 2 * (3 * m + 1) := by
        calc 4 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 * (3 * m + 4) * (3 * m + 1)
            = (4 * ((2 * m + 1) ^ 2 * (3 * m + 4)))
                * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by ring
          _ ≤ (4 * ((2 * m + 2) ^ 2 * (3 * m + 1))) * 16 ^ m :=
              Nat.mul_le_mul (by nlinarith) ih
          _ = 16 ^ (m + 1) * (m + 1) ^ 2 * (3 * m + 1) := by ring
      have h4 : ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1) * (3 * m + 1)
          ≤ 16 ^ (m + 1) * (m + 1) ^ 2 * (3 * m + 1) := by rw [h2]; exact h3
      have h5 : ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1)
          ≤ 16 ^ (m + 1) * (m + 1) ^ 2 :=
        Nat.le_of_mul_le_mul_right h4 (by omega)
      have h6 : (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
          ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
        calc (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1))
            = ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (3 * (m + 1) + 1) := by ring
          _ ≤ 16 ^ (m + 1) * (m + 1) ^ 2 := h5
          _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
      exact Nat.le_of_mul_le_mul_left h6 (by positivity)

/-- Every binomial coefficient satisfies `C(n,i)^2 (n+1) ≤ 2 · 4^n`. -/
theorem choose_sq_mul_succ_le (n i : ℕ) : (n.choose i) ^ 2 * (n + 1) ≤ 2 * 4 ^ n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have hmid : (m + m).choose i ≤ Nat.centralBinom m := by
      have := Nat.choose_le_middle i (m + m)
      rw [Nat.centralBinom, show 2 * m = m + m by ring]
      simpa [show (m + m) / 2 = m by omega] using this
    calc ((m + m).choose i) ^ 2 * (m + m + 1)
        ≤ (Nat.centralBinom m) ^ 2 * (3 * m + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hmid 2) (by omega)
      _ ≤ 16 ^ m := centralBinom_sq_le m
      _ ≤ 2 * 4 ^ (m + m) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, show 2 * m = m + m by ring]
          omega
  · subst hm
    have hmid : (2 * m + 1).choose i ≤ 2 * Nat.centralBinom m := by
      have h1 : (2 * m + 1).choose i ≤ (2 * m + 1).choose m := by
        have := Nat.choose_le_middle i (2 * m + 1)
        simpa [Nat.add_mul_div_left, Nat.mul_add_div] using this
      have hsym : (2 * m + 1).choose m = (2 * m + 1).choose (m + 1) := by
        rw [← Nat.choose_symm (by omega)]; congr 1; omega
      have hp : (2 * m + 1).choose (m + 1) = (2 * m).choose m + (2 * m).choose (m + 1) := by
        rw [show 2 * m + 1 = 2 * m + 1 by ring, Nat.choose_succ_succ']
      have h2 : (2 * m).choose (m + 1) ≤ (2 * m).choose m := by
        have := Nat.choose_le_middle (m + 1) (2 * m)
        simpa [Nat.mul_div_cancel_left] using this
      rw [Nat.centralBinom]
      omega
    calc ((2 * m + 1).choose i) ^ 2 * (2 * m + 1 + 1)
        ≤ (2 * Nat.centralBinom m) ^ 2 * (2 * (3 * m + 1)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hmid 2) (by omega)
      _ = 8 * ((Nat.centralBinom m) ^ 2 * (3 * m + 1)) := by ring
      _ ≤ 8 * 16 ^ m := Nat.mul_le_mul_left _ (centralBinom_sq_le m)
      _ = 2 * 4 ^ (2 * m + 1) := by
          rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, pow_succ]; ring

/-- The sum of the binomial coefficients `C(2m+1, i)` for `i ≤ m + D`. -/
theorem sum_choose_tail_le (m D : ℕ) :
    ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i ≤ 4 ^ m + D * ((2 * m + 1).choose m) := by
  have hsplit : ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i
      = (∑ i ∈ range (m + 1), (2 * m + 1).choose i)
        + ∑ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i := by
    rw [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega)).symm
  rw [hsplit, Nat.sum_range_choose_halfway m]
  gcongr
  calc ∑ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i
      ≤ ∑ _i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose m := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := Nat.choose_le_middle i (2 * m + 1)
        simpa [Nat.add_mul_div_left, Nat.mul_add_div] using this
    _ = D * ((2 * m + 1).choose m) := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
        congr 1
        omega

/-- Consequence: if `32 D² ≤ n+1` then `4 D C(n,i) ≤ 2^n`. -/
theorem four_mul_choose_le (n i D : ℕ) (h : 32 * D ^ 2 ≤ n + 1) :
    4 * D * (n.choose i) ≤ 2 ^ n := by
  have hb := choose_sq_mul_succ_le n i
  have key : (4 * D * (n.choose i)) ^ 2 * (n + 1) ≤ (2 ^ n) ^ 2 * (n + 1) := by
    calc (4 * D * (n.choose i)) ^ 2 * (n + 1)
        = 16 * D ^ 2 * ((n.choose i) ^ 2 * (n + 1)) := by ring
      _ ≤ 16 * D ^ 2 * (2 * 4 ^ n) := Nat.mul_le_mul_left _ hb
      _ = (32 * D ^ 2) * 4 ^ n := by ring
      _ ≤ (n + 1) * 4 ^ n := Nat.mul_le_mul_right _ h
      _ = (2 ^ n) ^ 2 * (n + 1) := by
          rw [← pow_mul, show n * 2 = 2 * n by ring, pow_mul]; ring
  have h2 : (4 * D * (n.choose i)) ^ 2 ≤ (2 ^ n) ^ 2 :=
    Nat.le_of_mul_le_mul_right key (by omega)
  exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).1 h2

end CS

import Mathlib

/-!
Constant depth circuits with unbounded fan-in AND / OR / NOT gates and `MOD q` gates,
i.e. the class `AC⁰[q]`.

A circuit is a directed acyclic graph, encoded by listing its gates in topological order:
gate number `i` may only refer to gates with a strictly smaller index.
-/

namespace CS

open Finset

/-- A gate whose children are among the gates with index `< k`. -/
inductive GateSpec (n : ℕ) (k : ℕ) where
  /-- the `i`-th input variable -/
  | inp : Fin n → GateSpec n k
  /-- a constant -/
  | cst : Bool → GateSpec n k
  /-- negation of gate `j` -/
  | notg : Fin k → GateSpec n k
  /-- unbounded fan-in OR of a set of gates -/
  | org : Finset (Fin k) → GateSpec n k
  /-- unbounded fan-in AND of a set of gates -/
  | andg : Finset (Fin k) → GateSpec n k
  /-- `MOD q` gate: outputs `true` iff the number of `true` inputs (with multiplicity,
  hence a list) is not divisible by `q` -/
  | modg : List (Fin k) → GateSpec n k

/-- A circuit on `n` Boolean inputs. -/
structure Circuit (n : ℕ) where
  /-- number of gates -/
  size : ℕ
  /-- the specification of each gate; children have smaller indices -/
  gate : (i : Fin size) → GateSpec n i.val
  /-- the output gate -/
  out : Fin size

namespace Circuit

variable {n : ℕ}

/-- View a child index of gate `i` as a gate index. -/
def up (C : Circuit n) (i : Fin C.size) (j : Fin i.val) : Fin C.size :=
  ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- The Boolean value computed at gate `i`, with `MOD q` gates. -/
noncomputable def gval (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size) : Bool :=
  match C.gate i with
  | .inp j => x j
  | .cst b => b
  | .notg j => !(C.gval q x (C.up i j))
  | .org S => S.sup (fun j => C.gval q x (C.up i j))
  | .andg S => S.inf (fun j => C.gval q x (C.up i j))
  | .modg L => decide (¬ q ∣ (L.filter (fun j => C.gval q x (C.up i j))).length)
termination_by i.val
decreasing_by all_goals exact j.isLt

/-- The depth of gate `i`: the maximal number of unbounded fan-in gates on a path from an
input to `i`.  (Negation gates are free; this only makes the lower bound stronger.) -/
def gdepth (C : Circuit n) (i : Fin C.size) : ℕ :=
  match C.gate i with
  | .inp _ => 0
  | .cst _ => 0
  | .notg j => C.gdepth (C.up i j)
  | .org S => 1 + S.sup (fun j => C.gdepth (C.up i j))
  | .andg S => 1 + S.sup (fun j => C.gdepth (C.up i j))
  | .modg L => 1 + (L.map (fun j => C.gdepth (C.up i j))).foldr max 0
termination_by i.val
decreasing_by all_goals exact j.isLt

/-- The Boolean function computed by the circuit. -/
noncomputable def eval (C : Circuit n) (q : ℕ) (x : Fin n → Bool) : Bool := C.gval q x C.out

/-- The depth of the circuit. -/
def depth (C : Circuit n) : ℕ := C.gdepth C.out

end Circuit

/-- The number of `true` coordinates. -/
def popc {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, (if x i then 1 else 0)

/-- The `MOD p` function: `true` iff the number of ones is *not* divisible by `p`. -/
def ModFun (p : ℕ) (n : ℕ) (x : Fin n → Bool) : Bool := decide (¬ p ∣ popc x)

/-- Membership in `AC⁰[q]`: a family of Boolean functions computed by circuits of
polynomial size and constant depth with AND/OR/NOT and `MOD q` gates. -/
def InAC0mod (q : ℕ) (f : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∃ d c k : ℕ, ∀ n : ℕ, ∃ C : Circuit n,
    C.size ≤ c * n ^ k + c ∧ C.depth ≤ d ∧ ∀ x, C.eval q x = f n x

end CS

import Mathlib

/-!
Degree filtration on the space of `F`-valued functions on the Boolean cube.

Instead of multivariate polynomials we work directly with the filtration of the function
space `(Fin n → Bool) → F` by the spans of multilinear monomials of bounded degree.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- The multilinear monomial function attached to a subset `S`: `x ↦ ∏_{i ∈ S} x i`. -/
def mono (F : Type*) [Field F] {n : ℕ} (S : Finset (Fin n)) : (Fin n → Bool) → F :=
  fun x => ∏ i ∈ S, (if x i then (1 : F) else 0)

/-- Functions on the cube of "degree at most `d`": the span of the multilinear monomials
of degree at most `d`. -/
def Deg (F : Type*) [Field F] (n d : ℕ) : Submodule F ((Fin n → Bool) → F) :=
  Submodule.span F {f | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = mono F S}

theorem mono_mem_Deg {d : ℕ} {S : Finset (Fin n)} (h : S.card ≤ d) :
    mono F S ∈ Deg F n d :=
  Submodule.subset_span ⟨S, h, rfl⟩

theorem Deg_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : Deg F n d₁ ≤ Deg F n d₂ := by
  apply Submodule.span_mono
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

theorem mem_Deg_of_le {d₁ d₂ : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n d₁)
    (h : d₁ ≤ d₂) : f ∈ Deg F n d₂ := Deg_mono h hf

theorem mono_empty : mono F (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mono]

theorem mono_apply (S : Finset (Fin n)) (x : Fin n → Bool) :
    mono F S x = if ∀ i ∈ S, x i = true then 1 else 0 := by
  by_cases h : ∀ i ∈ S, x i = true
  · rw [if_pos h]
    simp only [mono]
    exact Finset.prod_eq_one (fun i hi => by rw [h i hi]; rfl)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hxi⟩ := h
    exact Finset.prod_eq_zero hi (by simp [Bool.eq_false_iff.2 hxi])

theorem mono_mul (S T : Finset (Fin n)) : (mono F S) * (mono F T) = mono F (S ∪ T) := by
  funext x
  simp only [Pi.mul_apply, mono_apply, Finset.forall_mem_union]
  by_cases hS : ∀ i ∈ S, x i = true <;> by_cases hT : ∀ i ∈ T, x i = true
  · rw [if_pos hS, if_pos hT, if_pos ⟨hS, hT⟩, one_mul]
  · rw [if_neg hT, if_neg (fun h : (∀ i ∈ S, x i = true) ∧ ∀ i ∈ T, x i = true => hT h.2),
      mul_zero]
  · rw [if_neg hS, if_neg (fun h : (∀ i ∈ S, x i = true) ∧ ∀ i ∈ T, x i = true => hS h.1),
      zero_mul]
  · rw [if_neg hS, if_neg (fun h : (∀ i ∈ S, x i = true) ∧ ∀ i ∈ T, x i = true => hS h.1),
      zero_mul]

theorem Deg_one_mem {d : ℕ} : (1 : (Fin n → Bool) → F) ∈ Deg F n d := by
  rw [← mono_empty]
  exact mono_mem_Deg (by simp)

theorem Deg_const_mem {d : ℕ} (c : F) : (fun _ => c) ∈ Deg F n d := by
  have : (fun _ => c) = c • (1 : (Fin n → Bool) → F) := by funext x; simp
  rw [this]
  exact Submodule.smul_mem _ _ Deg_one_mem

theorem Deg_mul {d₁ d₂ : ℕ} {f g : (Fin n → Bool) → F} (hf : f ∈ Deg F n d₁)
    (hg : g ∈ Deg F n d₂) : f * g ∈ Deg F n (d₁ + d₂) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨T, hT, rfl⟩ := hg
          rw [mono_mul]
          exact mono_mem_Deg (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hS hT))
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

theorem Deg_pow {d k : ℕ} {f : (Fin n → Bool) → F} (hf : f ∈ Deg F n d) :
    f ^ k ∈ Deg F n (k * d) := by
  induction k with
  | zero => simpa using (Deg_one_mem : (1 : (Fin n → Bool) → F) ∈ Deg F n 0)
  | succ k ih =>
      have := Deg_mul ih hf
      have h2 : k * d + d = (k + 1) * d := by ring
      rw [h2] at this
      simpa [pow_succ] using this

theorem Deg_prod {ι : Type*} {s : Finset ι} {f : ι → (Fin n → Bool) → F} {e : ℕ}
    (hf : ∀ i ∈ s, f i ∈ Deg F n e) : (∏ i ∈ s, f i) ∈ Deg F n (s.card * e) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Deg_one_mem : (1 : (Fin n → Bool) → F) ∈ Deg F n 0)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : f a ∈ Deg F n e := hf a (by simp)
      have h2 : (∏ i ∈ s, f i) ∈ Deg F n (s.card * e) :=
        ih (fun i hi => hf i (by simp [hi]))
      have := Deg_mul h1 h2
      have he : e + s.card * e = (s.card + 1) * e := by ring
      rwa [he] at this

theorem Deg_sum {ι : Type*} {s : Finset ι} {f : ι → (Fin n → Bool) → F} {e : ℕ}
    (hf : ∀ i ∈ s, f i ∈ Deg F n e) : (∑ i ∈ s, f i) ∈ Deg F n e :=
  Submodule.sum_mem _ hf

/-- The indicator function of a point of the cube. -/
def delta (F : Type*) [Field F] {n : ℕ} (a : Fin n → Bool) : (Fin n → Bool) → F :=
  fun x => if x = a then 1 else 0

theorem delta_mem_Deg (a : Fin n → Bool) : delta F a ∈ Deg F n n := by
  have hfact : ∀ i : Fin n,
      (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) ∈ Deg F n 1 := by
    intro i
    by_cases h : a i = true
    · have : (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) = mono F {i} := by
        funext x; simp [mono_apply, h]
      rw [this]; exact mono_mem_Deg (by simp)
    · have h' : a i = false := by simpa using h
      have : (fun x : Fin n → Bool => if x i = a i then (1:F) else 0) = 1 - mono F {i} := by
        funext x; simp only [mono_apply, h', Pi.sub_apply, Pi.one_apply]
        cases hx : x i <;> simp [hx]
      rw [this]
      exact Submodule.sub_mem _ Deg_one_mem (mono_mem_Deg (by simp))
  have hprod := Deg_prod (F := F) (s := (univ : Finset (Fin n)))
    (f := fun i => (fun x : Fin n → Bool => if x i = a i then (1:F) else 0)) (e := 1)
    (fun i _ => hfact i)
  have heq :
      (∏ i ∈ (univ : Finset (Fin n)), (fun x : Fin n → Bool => if x i = a i then (1:F) else 0))
        = delta F a := by
    funext x
    simp only [Finset.prod_apply, delta]
    by_cases h : x = a
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [heq] at hprod
  simpa using hprod

theorem Deg_top : Deg F n n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have : f = ∑ a : (Fin n → Bool), f a • delta F a := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp [delta]
    · intro b _ hb; simp [delta, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [this]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (delta_mem_Deg a))

/-- The number of subsets of `Fin n` of size at most `d`. -/
theorem card_filter_card_le (n d : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).card
      = ∑ i ∈ range (d + 1), n.choose i := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (d+1))
    (by intro S hS; simp only [mem_coe, mem_filter] at hS ⊢; simp [hS.2])]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [mem_range, Nat.lt_succ_iff] at hi
  have : ({S ∈ {S : Finset (Fin n) | S.card ≤ d} | S.card = i} : Finset (Finset (Fin n)))
      = Finset.powersetCard i univ := by
    ext S
    simp only [mem_filter, mem_univ, true_and, Finset.mem_powersetCard]
    constructor
    · rintro ⟨-, h⟩; exact ⟨Finset.subset_univ S, h⟩
    · rintro ⟨-, h⟩; exact ⟨h ▸ hi, h⟩
  rw [this, Finset.card_powersetCard]
  simp

theorem Deg_finrank_le (F : Type*) [Field F] (n d : ℕ) :
    Module.finrank F (Deg F n d) ≤ ∑ i ∈ range (d + 1), n.choose i := by
  classical
  have hset : {f : (Fin n → Bool) → F | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = mono F S}
      = ↑((Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).image (mono F)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_filter,
      mem_univ, true_and]
    constructor
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩; exact ⟨S, hS, rfl⟩
  have hd : Deg F n d = Submodule.span F
      (↑((Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)).image (mono F)) :
        Set ((Fin n → Bool) → F)) := by
    rw [Deg, hset]
  rw [hd]
  refine le_trans (finrank_span_le_card _) ?_
  rw [← card_filter_card_le n d, Finset.toFinset_coe]
  exact Finset.card_image_le

/-- Key counting consequence: if every function on the cube agrees on `A` with some function
of degree at most `d`, then `A` is small. -/
theorem card_le_of_agree (F : Type*) [Field F] {n d : ℕ} (A : Finset (Fin n → Bool))
    (h : ∀ f : (Fin n → Bool) → F, ∃ g ∈ Deg F n d, ∀ x ∈ A, g x = f x) :
    A.card ≤ ∑ i ∈ range (d + 1), n.choose i := by
  classical
  set res : ((Fin n → Bool) → F) →ₗ[F] ({x // x ∈ A} → F) :=
    { toFun := fun f x => f x.1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } with hres
  set L : (Deg F n d) →ₗ[F] ({x // x ∈ A} → F) := res.comp (Deg F n d).subtype with hL
  have hsurj : Function.Surjective L := by
    intro f'
    obtain ⟨g, hg, hgf⟩ := h (fun x => if hx : x ∈ A then f' ⟨x, hx⟩ else 0)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext x
    have := hgf x.1 x.2
    simpa [hL, hres, x.2] using this
  have h1 : Module.finrank F ({x // x ∈ A} → F) ≤ Module.finrank F (Deg F n d) := by
    have := LinearMap.finrank_range_le L
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have h2 : Module.finrank F ({x // x ∈ A} → F) = A.card := by
    rw [Module.finrank_pi]; simp
  rw [h2] at h1
  exact h1.trans (Deg_finrank_le F n d)

end CS

import Mathlib
import RequestProject.Poly
import RequestProject.Circuit
import RequestProject.Count

/-!
Razborov's approximation lemma: a circuit of size `S` and depth `d` with AND/OR/NOT and
`MOD q` gates is computed, on all but a `S / 2^t` fraction of the inputs, by a function of
degree at most `((q-1) t) ^ d` over a field of characteristic `q`.
-/

namespace CS

open Finset
open scoped Classical

/-- `0/1` valued indicator of a Boolean. -/
def ind (F : Type*) [Field F] (b : Bool) : F := if b then 1 else 0

theorem ind_not {F : Type*} [Field F] (b : Bool) : ind F (!b) = 1 - ind F b := by
  cases b <;> simp [ind]

/-- In characteristic `q`, `(k : F)^(q-1)` is `0` if `q ∣ k` and `1` otherwise. -/
theorem natCast_pow_card_sub_one {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q]
    (k : ℕ) : ((k : F)) ^ (q - 1) = if q ∣ k then 0 else 1 := by
  have hp := Fact.out (p := q.Prime)
  have h : ((k : F)) = (ZMod.castHom (dvd_refl q) F) (k : ZMod q) := by simp
  split_ifs with hd
  · have h0 : (k : F) = 0 := by
      rw [h, (ZMod.natCast_eq_zero_iff k q).2 hd, map_zero]
    rw [h0]
    exact zero_pow (by have := hp.two_le; omega)
  · have hk : ((k : ZMod q)) ≠ 0 := fun hc => hd ((ZMod.natCast_eq_zero_iff k q).1 hc)
    rw [h, ← map_pow, ZMod.pow_card_sub_one_eq_one hk, map_one]

/-- Summing indicators over a selected set counts the selected witnesses. -/
theorem sum_ind_eq {F : Type*} [Field F] {k : ℕ} (S : Finset (Fin k)) (sel w : Fin k → Bool) :
    ∑ j ∈ S.filter (fun j => sel j = true), ind F (w j)
      = ((S.filter (fun j => sel j = true ∧ w j = true)).card : F) := by
  simp only [ind]
  rw [Finset.sum_boole]
  congr 2
  rw [Finset.filter_filter]

/-- In characteristic `q`, the product `∏ (1 - cₖ^{q-1})` detects whether all `cₖ` are
divisible by `q`. -/
theorem prod_dvd_char {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] {t : ℕ}
    (c : Fin t → ℕ) :
    ∏ k : Fin t, (1 - ((c k : F)) ^ (q - 1)) = if (∀ k, q ∣ c k) then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one (fun k _ => ?_)
    rw [natCast_pow_card_sub_one q (c k), if_pos (h k), sub_zero]
  · push_neg at h
    obtain ⟨k, hk⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    rw [natCast_pow_card_sub_one q (c k), if_neg hk, sub_self]

theorem list_sum_ind {F : Type*} [Field F] {k : ℕ} (L : List (Fin k)) (w : Fin k → Bool) :
    (L.map (fun j => ind F (w j))).sum = ((L.filter w).length : F) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.filter_cons]
      cases h : w a <;> simp [ind, add_comm]

theorem list_sum_apply {α β : Type*} [AddCommMonoid β] (l : List (α → β)) (x : α) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The value of the randomized product used at an `OR`/`AND` gate, assuming the children are
computed correctly. -/
theorem prod_dvd_eval {F : Type*} [Field F] (q : ℕ) [Fact q.Prime] [CharP F q] {t k : ℕ}
    (S : Finset (Fin k)) (sel : Fin t → Fin k → Bool) (g : Fin k → F) (w : Fin k → Bool)
    (hg : ∀ j ∈ S, g j = ind F (w j)) :
    ∏ κ : Fin t, (1 - (∑ j ∈ S.filter (fun j => sel κ j = true), g j) ^ (q - 1))
      = if (∀ κ : Fin t, q ∣ (S.filter (fun j => sel κ j = true ∧ w j = true)).card)
        then 1 else 0 := by
  have hstep : ∀ κ : Fin t, (∑ j ∈ S.filter (fun j => sel κ j = true), g j)
      = ((S.filter (fun j => sel κ j = true ∧ w j = true)).card : F) := by
    intro κ
    rw [← sum_ind_eq S (sel κ) w]
    exact Finset.sum_congr rfl (fun j hj => hg j (Finset.mem_filter.1 hj).1)
  simp only [hstep]
  exact prod_dvd_char q (fun κ => (S.filter (fun j => sel κ j = true ∧ w j = true)).card)

namespace Circuit

variable {n : ℕ}

/-- The randomness used by the approximating polynomial: for each gate and each of the `t`
rounds, a random subset of the gate indices. -/
abbrev Rand (C : Circuit n) (t : ℕ) := Fin C.size → Fin t → Fin C.size → Bool

/-- The random low degree approximation of the value at gate `i`. -/
noncomputable def gpoly (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) : (Fin n → Bool) → F :=
  match C.gate i with
  | .inp j => mono F {j}
  | .cst b => fun _ => ind F b
  | .notg j => 1 - gpoly F C q t ρ (C.up i j)
  | .org S => 1 - ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true), gpoly F C q t ρ (C.up i j)) ^ (q - 1))
  | .andg S => ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
        (1 - gpoly F C q t ρ (C.up i j))) ^ (q - 1))
  | .modg L => ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum) ^ (q - 1)
termination_by i.val
decreasing_by all_goals exact j.isLt

theorem gpoly_inp (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (j : Fin n) (hg : C.gate i = .inp j) :
    gpoly F C q t ρ i = mono F {j} := by rw [gpoly, hg]

theorem gpoly_cst (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (b : Bool) (hg : C.gate i = .cst b) :
    gpoly F C q t ρ i = fun _ => ind F b := by rw [gpoly, hg]

theorem gpoly_notg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (j : Fin i.val) (hg : C.gate i = .notg j) :
    gpoly F C q t ρ i = 1 - gpoly F C q t ρ (C.up i j) := by rw [gpoly, hg]

theorem gpoly_org (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (S : Finset (Fin i.val)) (hg : C.gate i = .org S) :
    gpoly F C q t ρ i = 1 - ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
        gpoly F C q t ρ (C.up i j)) ^ (q - 1)) := by rw [gpoly, hg]

theorem gpoly_andg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (S : Finset (Fin i.val)) (hg : C.gate i = .andg S) :
    gpoly F C q t ρ i = ∏ k : Fin t, (1 -
      (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
        (1 - gpoly F C q t ρ (C.up i j))) ^ (q - 1)) := by rw [gpoly, hg]

theorem gpoly_modg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (i : Fin C.size) (L : List (Fin i.val)) (hg : C.gate i = .modg L) :
    gpoly F C q t ρ i = ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum) ^ (q - 1) := by
  rw [gpoly, hg]

theorem gval_inp (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size) (j : Fin n)
    (hg : C.gate i = .inp j) : C.gval q x i = x j := by rw [gval, hg]

theorem gval_cst (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size) (b : Bool)
    (hg : C.gate i = .cst b) : C.gval q x i = b := by rw [gval, hg]

theorem gval_notg (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size) (j : Fin i.val)
    (hg : C.gate i = .notg j) : C.gval q x i = !(C.gval q x (C.up i j)) := by rw [gval, hg]

theorem gval_org (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size)
    (S : Finset (Fin i.val)) (hg : C.gate i = .org S) :
    C.gval q x i = S.sup (fun j => C.gval q x (C.up i j)) := by rw [gval, hg]

theorem gval_andg (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size)
    (S : Finset (Fin i.val)) (hg : C.gate i = .andg S) :
    C.gval q x i = S.inf (fun j => C.gval q x (C.up i j)) := by rw [gval, hg]

theorem gval_modg (C : Circuit n) (q : ℕ) (x : Fin n → Bool) (i : Fin C.size)
    (L : List (Fin i.val)) (hg : C.gate i = .modg L) :
    C.gval q x i = decide (¬ q ∣ (L.filter (fun j => C.gval q x (C.up i j))).length) := by
  rw [gval, hg]

theorem list_foldr_max_le {α : Type*} (l : List α) (f : α → ℕ) (a : α) (ha : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 ha with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem Deg_list_sum {F : Type*} [Field F] {e : ℕ} (l : List ((Fin n → Bool) → F))
    (hl : ∀ f ∈ l, f ∈ Deg F n e) : l.sum ∈ Deg F n e := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons]
      exact Submodule.add_mem _ (hl a (by simp)) (ih (fun f hf => hl f (by simp [hf])))

/-- The approximating function has low degree. -/
theorem gpoly_mem_Deg (F : Type*) [Field F] (C : Circuit n) {q t : ℕ} (hq : 2 ≤ q)
    (ht : 1 ≤ t) (ρ : Rand C t) (i : Fin C.size) :
    gpoly F C q t ρ i ∈ Deg F n (((q - 1) * t) ^ (C.gdepth i)) := by
  have hb : 1 ≤ (q - 1) * t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have H : ∀ N : ℕ, ∀ i : Fin C.size, i.val < N →
      gpoly F C q t ρ i ∈ Deg F n (((q - 1) * t) ^ (C.gdepth i)) := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi
      have hchild : ∀ j : Fin i.val, (C.up i j).val < N := by
        intro j; have := j.isLt; simp only [Circuit.up]; omega
      rw [gpoly, gdepth]
      match hg : C.gate i with
      | .inp j =>
          simp only []
          exact mono_mem_Deg (by simp)
      | .cst b =>
          simp only []
          exact Deg_const_mem _
      | .notg j =>
          simp only []
          exact Submodule.sub_mem _ Deg_one_mem (ih (C.up i j) (hchild j))
      | .org S =>
          simp only []
          set D := S.sup (fun j => C.gdepth (C.up i j)) with hD
          have hchildD : ∀ j ∈ S, gpoly F C q t ρ (C.up i j) ∈ Deg F n (((q-1)*t)^D) :=
            fun j hj => mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (Finset.le_sup (f := fun j => C.gdepth (C.up i j)) hj))
          have hterm : ∀ k : Fin t,
              (1 - (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
                gpoly F C q t ρ (C.up i j)) ^ (q-1)) ∈ Deg F n ((q-1) * ((q-1)*t)^D) :=
            fun k => Submodule.sub_mem _ Deg_one_mem
              (Deg_pow (Deg_sum (fun j hj => hchildD j (Finset.mem_filter.1 hj).1)))
          have hprod := Deg_prod (s := (univ : Finset (Fin t))) (fun k _ => hterm k)
          have hEq : (univ : Finset (Fin t)).card * ((q-1) * ((q-1)*t)^D) = ((q-1)*t)^(1+D) := by
            rw [Finset.card_univ, Fintype.card_fin, pow_add, pow_one]; ring
          rw [hEq] at hprod
          exact Submodule.sub_mem _ Deg_one_mem hprod
      | .andg S =>
          simp only []
          set D := S.sup (fun j => C.gdepth (C.up i j)) with hD
          have hchildD : ∀ j ∈ S, (1 - gpoly F C q t ρ (C.up i j)) ∈ Deg F n (((q-1)*t)^D) :=
            fun j hj => Submodule.sub_mem _ Deg_one_mem (mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (Finset.le_sup (f := fun j => C.gdepth (C.up i j)) hj)))
          have hterm : ∀ k : Fin t,
              (1 - (∑ j ∈ S.filter (fun j => ρ i k (C.up i j) = true),
                (1 - gpoly F C q t ρ (C.up i j))) ^ (q-1)) ∈ Deg F n ((q-1) * ((q-1)*t)^D) :=
            fun k => Submodule.sub_mem _ Deg_one_mem
              (Deg_pow (Deg_sum (fun j hj => hchildD j (Finset.mem_filter.1 hj).1)))
          have hprod := Deg_prod (s := (univ : Finset (Fin t))) (fun k _ => hterm k)
          have hEq : (univ : Finset (Fin t)).card * ((q-1) * ((q-1)*t)^D) = ((q-1)*t)^(1+D) := by
            rw [Finset.card_univ, Fintype.card_fin, pow_add, pow_one]; ring
          rw [hEq] at hprod
          exact hprod
      | .modg L =>
          simp only []
          set M := (L.map (fun j => C.gdepth (C.up i j))).foldr max 0 with hM
          have hsum : ((L.map (fun j => gpoly F C q t ρ (C.up i j))).sum)
              ∈ Deg F n (((q-1)*t)^M) := by
            refine Deg_list_sum _ ?_
            intro f hf
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
            exact mem_Deg_of_le (ih (C.up i j) (hchild j))
              (Nat.pow_le_pow_right hb (list_foldr_max_le L (fun j => C.gdepth (C.up i j)) j hj))
          refine mem_Deg_of_le (Deg_pow hsum) ?_
          rw [pow_add, pow_one]
          exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ ht)
  exact H (i.val + 1) i (Nat.lt_succ_self _)

/-- The randomized polynomial is correct at gate `i` on input `x`. -/
def Good (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t) (x : Fin n → Bool)
    (i : Fin C.size) : Prop := gpoly F C q t ρ i x = ind F (C.gval q x i)

/-- Gate `i` does not introduce an error: if all its children are correct, so is it. -/
def LocalGood (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (x : Fin n → Bool) (i : Fin C.size) : Prop :=
  (∀ j : Fin i.val, Good F C q t ρ x (C.up i j)) → Good F C q t ρ x i

theorem all_good (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) (ρ : Rand C t)
    (x : Fin n → Bool) (h : ∀ i, LocalGood F C q t ρ x i) : ∀ i, Good F C q t ρ x i := by
  have H : ∀ N : ℕ, ∀ i : Fin C.size, i.val < N → Good F C q t ρ x i := by
    intro N
    induction N with
    | zero => intro i hi; omega
    | succ N ih =>
      intro i hi
      refine h i (fun j => ih (C.up i j) ?_)
      have := j.isLt
      simp only [Circuit.up]
      omega
  exact fun i => H (i.val + 1) i (Nat.lt_succ_self _)

/-- The dichotomy at an `OR` gate. -/
theorem gate_dichotomy_org (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) (S : Finset (Fin i.val))
    (hg : C.gate i = .org S) :
    (∀ ρ : Rand C t, LocalGood F C q t ρ x i) ∨
    ∃ (S : Finset (Fin i.val)) (w : Fin i.val → Bool) (j₀ : Fin i.val),
      j₀ ∈ S ∧ w j₀ = true ∧
      ∀ ρ : Rand C t, ¬ LocalGood F C q t ρ x i →
        ∀ κ : Fin t, q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card := by
  set w : Fin i.val → Bool := fun j => C.gval q x (C.up i j) with hw
  have hmain : ∀ ρ : Rand C t, (∀ j : Fin i.val, Good F C q t ρ x (C.up i j)) →
      gpoly F C q t ρ i x =
        1 - (if (∀ κ : Fin t,
          q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card) then 1 else 0) := by
    intro ρ hch
    rw [gpoly_org F C q t ρ i S hg]
    simp only [Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply, Finset.sum_apply]
    congr 1
    exact prod_dvd_eval q S (fun κ j => ρ i κ (C.up i j))
      (fun j => gpoly F C q t ρ (C.up i j) x) w (fun j _ => hch j)
  by_cases hall : ∀ j ∈ S, w j = false
  · left
    intro ρ hch
    simp only [Good, hmain ρ hch, gval_org C q x i S hg]
    have hcnt : ∀ κ : Fin t,
        (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card = 0 := by
      intro κ
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj
      rw [hall j hj]
      simp
    rw [if_pos (fun κ => by rw [hcnt κ]; exact dvd_zero q)]
    have hsup : S.sup w = false :=
      le_antisymm (Finset.sup_le (fun j hj => by rw [hall j hj])) (by simp)
    rw [show (fun j => C.gval q x (C.up i j)) = w from rfl, hsup]
    simp [ind]
  · right
    push_neg at hall
    obtain ⟨j₀, hj₀S, hj₀⟩ := hall
    have h2 : w j₀ = true := by simpa [hw] using hj₀
    refine ⟨S, w, j₀, hj₀S, h2, ?_⟩
    intro ρ hbad
    by_contra hcon
    apply hbad
    intro hch
    simp only [Good, hmain ρ hch, gval_org C q x i S hg, if_neg hcon]
    have hsup : S.sup w = true := by
      have h1 : w j₀ ≤ S.sup w := Finset.le_sup hj₀S
      rw [h2] at h1
      rcases Bool.eq_false_or_eq_true (S.sup w) with hs | hs
      · exact hs
      · rw [hs] at h1; exact absurd h1 (by decide)
    rw [show (fun j => C.gval q x (C.up i j)) = w from rfl, hsup]
    simp [ind]

/-- The dichotomy at an `AND` gate. -/
theorem gate_dichotomy_andg (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) (S : Finset (Fin i.val))
    (hg : C.gate i = .andg S) :
    (∀ ρ : Rand C t, LocalGood F C q t ρ x i) ∨
    ∃ (S : Finset (Fin i.val)) (w : Fin i.val → Bool) (j₀ : Fin i.val),
      j₀ ∈ S ∧ w j₀ = true ∧
      ∀ ρ : Rand C t, ¬ LocalGood F C q t ρ x i →
        ∀ κ : Fin t, q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card := by
  set w : Fin i.val → Bool := fun j => !(C.gval q x (C.up i j)) with hw
  have hmain : ∀ ρ : Rand C t, (∀ j : Fin i.val, Good F C q t ρ x (C.up i j)) →
      gpoly F C q t ρ i x =
        (if (∀ κ : Fin t,
          q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card) then 1 else 0) := by
    intro ρ hch
    rw [gpoly_andg F C q t ρ i S hg]
    simp only [Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.pow_apply, Finset.sum_apply]
    refine prod_dvd_eval q S (fun κ j => ρ i κ (C.up i j))
      (fun j => 1 - gpoly F C q t ρ (C.up i j) x) w (fun j _ => ?_)
    dsimp only
    rw [show gpoly F C q t ρ (C.up i j) x = ind F (C.gval q x (C.up i j)) from hch j, ← ind_not]
  by_cases hall : ∀ j ∈ S, w j = false
  · left
    intro ρ hch
    have hallv : ∀ j ∈ S, C.gval q x (C.up i j) = true := by
      intro j hj
      simpa [hw] using hall j hj
    simp only [Good, hmain ρ hch, gval_andg C q x i S hg]
    have hcnt : ∀ κ : Fin t,
        (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card = 0 := by
      intro κ
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj
      rw [hall j hj]
      simp
    rw [if_pos (fun κ => by rw [hcnt κ]; exact dvd_zero q)]
    have hinf : S.inf (fun j => C.gval q x (C.up i j)) = true :=
      le_antisymm (by simp) (Finset.le_inf (fun j hj => by rw [hallv j hj]))
    rw [hinf]
    simp [ind]
  · right
    push_neg at hall
    obtain ⟨j₀, hj₀S, hj₀⟩ := hall
    have h2 : w j₀ = true := by simpa [hw] using hj₀
    have h3 : C.gval q x (C.up i j₀) = false := by simpa [hw] using h2
    refine ⟨S, w, j₀, hj₀S, h2, ?_⟩
    intro ρ hbad
    by_contra hcon
    apply hbad
    intro hch
    simp only [Good, hmain ρ hch, gval_andg C q x i S hg, if_neg hcon]
    have hinf : S.inf (fun j => C.gval q x (C.up i j)) = false := by
      have h1 : S.inf (fun j => C.gval q x (C.up i j)) ≤ C.gval q x (C.up i j₀) :=
        Finset.inf_le hj₀S
      rw [h3] at h1
      rcases Bool.eq_false_or_eq_true (S.inf (fun j => C.gval q x (C.up i j))) with hs | hs
      · rw [hs] at h1; exact absurd h1 (by decide)
      · exact hs
    rw [hinf]
    simp [ind]

/-- Either the gate `i` never introduces an error on input `x`, or there is a witness making
the failure event a "all `t` random subsets select a multiple of `q` witnesses" event. -/
theorem gate_dichotomy (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) :
    (∀ ρ : Rand C t, LocalGood F C q t ρ x i) ∨
    ∃ (S : Finset (Fin i.val)) (w : Fin i.val → Bool) (j₀ : Fin i.val),
      j₀ ∈ S ∧ w j₀ = true ∧
      ∀ ρ : Rand C t, ¬ LocalGood F C q t ρ x i →
        ∀ κ : Fin t, q ∣ (S.filter (fun j => ρ i κ (C.up i j) = true ∧ w j = true)).card := by
  rcases hg : C.gate i with j | b | j | S | S | L
  · left; intro ρ _
    simp only [Good, gpoly_inp F C q t ρ i j hg, gval_inp C q x i j hg]
    simp [mono_apply, ind]
  · left; intro ρ _
    simp only [Good, gpoly_cst F C q t ρ i b hg, gval_cst C q x i b hg]
  · left; intro ρ hch
    simp only [Good, gpoly_notg F C q t ρ i j hg, gval_notg C q x i j hg]
    simp only [Pi.sub_apply, Pi.one_apply]
    rw [show gpoly F C q t ρ (C.up i j) x = ind F (C.gval q x (C.up i j)) from hch j, ← ind_not]
  · exact gate_dichotomy_org F C q t x i S hg
  · exact gate_dichotomy_andg F C q t x i S hg
  · left; intro ρ hch
    simp only [Good, gpoly_modg F C q t ρ i L hg, gval_modg C q x i L hg]
    simp only [Pi.pow_apply]
    rw [list_sum_apply, List.map_map]
    have hmap : ((fun f => f x) ∘ fun j => gpoly F C q t ρ (C.up i j))
        = fun j => ind F (C.gval q x (C.up i j)) := by
      funext j; exact hch j
    rw [hmap, list_sum_ind, natCast_pow_card_sub_one q]
    by_cases hd : q ∣ (List.filter (fun j => C.gval q x (C.up i j)) L).length
    · rw [if_pos hd]; simp [ind, hd]
    · rw [if_neg hd]; simp [ind, hd]

/-- For every gate and every input, the fraction of random choices for which the gate fails
is at most `2^{-t}`. -/
theorem card_localbad_le (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (x : Fin n → Bool) (i : Fin C.size) :
    (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card * 2 ^ t
      ≤ Fintype.card (Rand C t) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  rcases gate_dichotomy F C q t x i with hgood | ⟨S, w, j₀, hj₀S, hw, hbad⟩
  · have he : (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro ρ _
      exact not_not_intro (hgood ρ)
    rw [he]; simp
  · refine card_gate_bad_le hq2 S (C.up i) ?_ w j₀ hj₀S hw i _ ?_
    · intro a b hab
      exact Fin.ext (by simpa [Circuit.up] using congrArg Fin.val hab)
    · intro ρ hρ
      exact hbad ρ (Finset.mem_filter.1 hρ).2

/-- For a suitable choice of the randomness, the approximation is correct on all but a
`size / 2^t` fraction of the inputs. -/
theorem exists_good_rand (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] :
    ∃ ρ : Rand C t,
      (univ.filter (fun x => gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ C.size * 2 ^ n := by
  have hx : ∀ x : Fin n → Bool,
      (univ.filter (fun ρ : Rand C t =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ C.size * Fintype.card (Rand C t) := by
    intro x
    have hsub : (univ.filter (fun ρ : Rand C t =>
          gpoly F C q t ρ C.out x ≠ ind F (C.eval q x)))
        ⊆ (univ : Finset (Fin C.size)).biUnion
            (fun i => univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)) := by
      intro ρ hρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
      by_contra hc
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      push_neg at hc
      exact hρ (all_good F C q t ρ x (fun i => hc i) C.out)
    calc (univ.filter (fun ρ : Rand C t =>
            gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t
        ≤ ((univ : Finset (Fin C.size)).biUnion
            (fun i => univ.filter (fun ρ : Rand C t =>
              ¬ LocalGood F C q t ρ x i))).card * 2 ^ t :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (∑ i : Fin C.size,
            (univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ (Finset.card_biUnion_le)
      _ = ∑ i : Fin C.size,
            ((univ.filter (fun ρ : Rand C t => ¬ LocalGood F C q t ρ x i)).card * 2 ^ t) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin C.size, Fintype.card (Rand C t) :=
          Finset.sum_le_sum (fun i _ => card_localbad_le F C q t x i)
      _ = C.size * Fintype.card (Rand C t) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hswap : ∑ x : Fin n → Bool, (univ.filter (fun ρ : Rand C t =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card
      = ∑ ρ : Rand C t, (univ.filter (fun x : Fin n → Bool =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hmain : ∑ ρ : Rand C t, ((univ.filter (fun x : Fin n → Bool =>
        gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t)
      ≤ ∑ _ρ : Rand C t, (C.size * 2 ^ n) := by
    rw [← Finset.sum_mul, ← hswap, Finset.sum_mul]
    calc ∑ x : Fin n → Bool, ((univ.filter (fun ρ : Rand C t =>
            gpoly F C q t ρ C.out x ≠ ind F (C.eval q x))).card * 2 ^ t)
        ≤ ∑ _x : Fin n → Bool, (C.size * Fintype.card (Rand C t)) :=
          Finset.sum_le_sum (fun x _ => hx x)
      _ = 2 ^ n * (C.size * Fintype.card (Rand C t)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          simp
      _ = Fintype.card (Rand C t) * (C.size * 2 ^ n) := by ring
      _ = ∑ _ρ : Rand C t, (C.size * 2 ^ n) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  obtain ⟨ρ, -, hρ⟩ := exists_le_of_sum_le (Finset.univ_nonempty (α := Rand C t)) hmain
  exact ⟨ρ, hρ⟩

/-- Razborov's approximation lemma. -/
theorem exists_approx (F : Type*) [Field F] (C : Circuit n) (q t : ℕ) [Fact q.Prime]
    [CharP F q] (ht : 1 ≤ t) :
    ∃ P : (Fin n → Bool) → F, P ∈ Deg F n (((q - 1) * t) ^ C.depth) ∧
      (univ.filter (fun x => P x ≠ ind F (C.eval q x))).card * 2 ^ t ≤ C.size * 2 ^ n := by
  obtain ⟨ρ, hρ⟩ := exists_good_rand F C q t
  exact ⟨gpoly F C q t ρ C.out,
    gpoly_mem_Deg F C (Nat.Prime.two_le Fact.out) ht ρ C.out, hρ⟩

end Circuit

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Poly
import RequestProject.Binom
import RequestProject.Circuit
import RequestProject.Approx
import RequestProject.Lower
import RequestProject.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- The field over which we approximate: an algebraic closure of `𝔽_q`. -/
noncomputable abbrev Fq (q : ℕ) [Fact q.Prime] := AlgebraicClosure (ZMod q)

instance FqCharP (q : ℕ) [Fact q.Prime] : CharP (Fq q) q :=
  inferInstanceAs (CharP (AlgebraicClosure (ZMod q)) q)

theorem exists_primitiveRoot_Fq (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    ∃ ζ : Fq q, IsPrimitiveRoot ζ p := by
  have : NeZero ((p : ZMod q)) := by
    constructor
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
      ((ZMod.natCast_eq_zero_iff p q).1 h)).symm
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod q)) p

/-- Padding an input with `r` ones. -/
def pad (p r : ℕ) : Fin p → Bool := fun i => decide (i.val < r)

theorem popc_pad {p r : ℕ} (h : r ≤ p) : popc (pad p r) = r := by
  simp only [popc, pad]
  rw [Fin.sum_univ_eq_sum_range (fun i => if (decide (i < r)) then 1 else 0) p]
  simp only [decide_eq_true_eq]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    show ({x ∈ range p | x < r}) = range r by ext x; simp; omega]
  simp

theorem popc_append {n p : ℕ} (x : Fin n → Bool) (b : Fin p → Bool) :
    popc (Fin.append x b) = popc x + popc b := by
  simp only [popc]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- Substituting constants for the last `p` inputs does not increase the degree. -/
theorem Deg_subst {F : Type*} [Field F] {n p D : ℕ} {P : (Fin (n + p) → Bool) → F}
    (hP : P ∈ Deg F (n + p) D) (b : Fin p → Bool) :
    (fun x : Fin n → Bool => P (Fin.append x b)) ∈ Deg F n D := by
  classical
  induction hP using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, rfl⟩ := hf
      set S₁ : Finset (Fin n) := univ.filter (fun j => Fin.castAdd p j ∈ S) with hS₁def
      have hcard : S₁.card ≤ D := by
        refine le_trans (Finset.card_le_card_of_injOn (fun j => Fin.castAdd p j) ?_ ?_) hS
        · intro j hj
          have hj' : j ∈ S₁ := hj
          rw [hS₁def, Finset.mem_filter] at hj'
          exact hj'.2
        · intro a _ c _ hac
          exact Fin.castAdd_inj.mp hac
      have key : ∀ x : Fin n → Bool, mono F S (Fin.append x b)
          = (if (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) then (1 : F) else 0)
            * mono F S₁ x := by
        intro x
        rw [mono_apply, mono_apply]
        have hiff : (∀ i ∈ S, (Fin.append x b) i = true)
            ↔ (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) ∧ (∀ j ∈ S₁, x j = true) := by
          constructor
          · intro hall
            refine ⟨fun k hk => ?_, fun j hj => ?_⟩
            · have := hall _ hk
              rwa [Fin.append_right] at this
            · rw [hS₁def, Finset.mem_filter] at hj
              have := hall _ hj.2
              rwa [Fin.append_left] at this
          · rintro ⟨h1, h2⟩ i hi
            induction i using Fin.addCases with
            | left j =>
                rw [Fin.append_left]
                exact h2 j (by rw [hS₁def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩)
            | right k =>
                rw [Fin.append_right]
                exact h1 k hi
        by_cases hb : (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true)
        · by_cases hx : (∀ j ∈ S₁, x j = true)
          · rw [if_pos (hiff.2 ⟨hb, hx⟩), if_pos hb, if_pos hx, mul_one]
          · rw [if_neg (fun hc => hx (hiff.1 hc).2), if_pos hb, if_neg hx, mul_zero]
        · rw [if_neg (fun hc => hb (hiff.1 hc).1), if_neg hb, zero_mul]
      have heq : (fun x : Fin n → Bool => mono F S (Fin.append x b))
          = (if (∀ k : Fin p, Fin.natAdd n k ∈ S → b k = true) then (1 : F) else 0)
            • mono F S₁ := by
        funext x; rw [key x]; rfl
      rw [heq]
      exact Submodule.smul_mem _ _ (mem_Deg_of_le (mono_mem_Deg (le_refl _)) hcard)
  | zero => exact Submodule.zero_mem _
  | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
  | smul c a _ ha => exact Submodule.smul_mem _ _ ha

/-- A polynomial is eventually dominated by `2^t`. -/
theorem poly_le_two_pow (B E : ℕ) : ∃ t : ℕ, 1 ≤ t ∧ B * (t + 1) ^ E ≤ 2 ^ t := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) E (r := 2) (by norm_num)
  have hc : (0 : ℝ) < 1 / ((B : ℝ) + 1) / 2 ^ E := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.def hc)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  set t := max N 1 with ht
  have ht1 : 1 ≤ t := le_max_right _ _
  have hb := hN t (le_max_left _ _)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ E),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ t)] at hb
  have key : (B : ℝ) * ((t : ℝ) + 1) ^ E ≤ 2 ^ t := by
    have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have h3 : ((t : ℝ) + 1) ^ E ≤ (2 * (t : ℝ)) ^ E := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hfin : (B : ℝ) * 2 ^ E * (1 / ((B : ℝ) + 1) / 2 ^ E * 2 ^ t)
        = ((B : ℝ) / ((B : ℝ) + 1)) * 2 ^ t := by field_simp
    calc (B : ℝ) * ((t : ℝ) + 1) ^ E ≤ (B : ℝ) * (2 * (t : ℝ)) ^ E := by
          nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * (t : ℝ)) E]
      _ = ((B : ℝ) * 2 ^ E) * (t : ℝ) ^ E := by rw [mul_pow]; ring
      _ ≤ ((B : ℝ) * 2 ^ E) * (1 / ((B : ℝ) + 1) / 2 ^ E * 2 ^ t) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((B : ℝ) / ((B : ℝ) + 1)) * 2 ^ t := hfin
      _ ≤ 2 ^ t := by
          have h1 : (B : ℝ) / ((B : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) t]
  exact_mod_cast key

/-- Choice of the parameters: `n = 2m+1` inputs and `t` rounds in the approximation. -/
theorem exists_params (p q c k d : ℕ) (hq : 2 ≤ q) :
    ∃ m t : ℕ, 1 ≤ m ∧ 1 ≤ t ∧
      8 * p * 2 ^ p * (c * (2 * m + 1 + p) ^ k + c) ≤ 2 ^ t ∧
      32 * (((q - 1) * t) ^ d) ^ 2 ≤ 2 * m + 2 := by
  set G := 32 * (q - 1) ^ (2 * d) + 1 + p with hG
  obtain ⟨t, ht1, ht⟩ := poly_le_two_pow (8 * p * 2 ^ p * (c * G ^ k + c)) (2 * d * k)
  refine ⟨16 * ((q - 1) * t) ^ (2 * d), t, ?_, ht1, ?_, ?_⟩
  · have : 1 ≤ ((q - 1) * t) ^ (2 * d) :=
      Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    omega
  · have hstep : 2 * (16 * ((q - 1) * t) ^ (2 * d)) + 1 + p ≤ G * (t + 1) ^ (2 * d) := by
      have h1 : ((q - 1) * t) ^ (2 * d) ≤ (q - 1) ^ (2 * d) * (t + 1) ^ (2 * d) := by
        rw [mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      have h2 : 1 ≤ (t + 1) ^ (2 * d) := Nat.one_le_pow _ _ (by omega)
      calc 2 * (16 * ((q - 1) * t) ^ (2 * d)) + 1 + p = 32 * ((q - 1) * t) ^ (2 * d) + 1 + p := by
            ring
        _ ≤ 32 * ((q - 1) ^ (2 * d) * (t + 1) ^ (2 * d)) + (1 + p) * (t + 1) ^ (2 * d) := by
            have h4 := Nat.mul_le_mul_left 32 h1
            have h3 : 1 + p ≤ (1 + p) * (t + 1) ^ (2 * d) :=
              Nat.le_mul_of_pos_right _ (by positivity)
            omega
        _ = G * (t + 1) ^ (2 * d) := by rw [hG]; ring
    calc 8 * p * 2 ^ p * (c * (2 * (16 * ((q - 1) * t) ^ (2 * d)) + 1 + p) ^ k + c)
        ≤ 8 * p * 2 ^ p * (c * (G * (t + 1) ^ (2 * d)) ^ k + c) := by gcongr
      _ = 8 * p * 2 ^ p * (c * G ^ k * (t + 1) ^ (2 * d * k) + c) := by
          rw [mul_pow, ← pow_mul]; ring_nf
      _ ≤ 8 * p * 2 ^ p * (c * G ^ k * (t + 1) ^ (2 * d * k) + c * (t + 1) ^ (2 * d * k)) := by
          gcongr
          exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = 8 * p * 2 ^ p * (c * G ^ k + c) * (t + 1) ^ (2 * d * k) := by ring
      _ ≤ 2 ^ t := ht
  · rw [← pow_mul, show d * 2 = 2 * d by ring]
    omega

/-- For every `s` there is a unique `r₀ < p` with `p ∣ s + r₀`. -/
theorem exists_unique_shift (p s : ℕ) [NeZero p] :
    ∃ r₀, r₀ < p ∧ p ∣ s + r₀ ∧ ∀ r, r < p → p ∣ s + r → r = r₀ := by
  have hcast : ∀ a : ℕ, (p ∣ s + a) ↔ ((a : ZMod p) = -(s : ZMod p)) := by
    intro a
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  refine ⟨((-(s : ZMod p)).val), ZMod.val_lt _, ?_, ?_⟩
  · rw [hcast, ZMod.natCast_val, ZMod.cast_id]
  · intro r hr hdvd
    rw [hcast] at hdvd
    rw [← hdvd, ZMod.val_cast_of_lt hr]

open Classical in
/-- **Razborov–Smolensky**: for distinct primes `p` and `q`, the `MOD p` function is not
computed by polynomial size constant depth circuits with unbounded fan-in AND/OR/NOT gates
and `MOD q` gates. -/
theorem razborov_smolensky (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ InAC0mod q (ModFun p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  rintro ⟨d, c, k, hfam⟩
  obtain ⟨m, t, hm1, ht1, hsize, hdeg⟩ := exists_params p q c k d hq2
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Fq p q hpq
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hζp
    exact zero_ne_one hζp
  obtain ⟨C, hCsize, hCdepth, hCeval⟩ := hfam (2 * m + 1 + p)
  obtain ⟨P, hPdeg, hPbad⟩ := Circuit.exists_approx (Fq q) C q t ht1
  have hqt : 1 ≤ (q - 1) * t := Nat.mul_pos (by omega) ht1
  set D := ((q - 1) * t) ^ d with hD
  have hPD : P ∈ Deg (Fq q) (2 * m + 1 + p) D :=
    mem_Deg_of_le hPdeg (Nat.pow_le_pow_right hqt hCdepth)
  set Bad := (univ.filter (fun y : Fin (2 * m + 1 + p) → Bool =>
      P y ≠ ind (Fq q) (C.eval q y))) with hBad
  set A := (univ.filter (fun x : Fin (2 * m + 1) → Bool => ∀ r ∈ range p,
      P (Fin.append x (pad p r))
        = ind (Fq q) (ModFun p (2 * m + 1 + p) (Fin.append x (pad p r))))) with hA
  -- Step 1 : the exceptional set is small
  have hbadsmall : 8 * (p * Bad.card) ≤ 2 ^ (2 * m + 1) := by
    have key : (8 * (p * Bad.card)) * 2 ^ t ≤ 2 ^ (2 * m + 1) * 2 ^ t := by
      calc (8 * (p * Bad.card)) * 2 ^ t = (8 * p) * (Bad.card * 2 ^ t) := by ring
        _ ≤ (8 * p) * (C.size * 2 ^ (2 * m + 1 + p)) := Nat.mul_le_mul_left _ hPbad
        _ = (8 * p * 2 ^ p * C.size) * 2 ^ (2 * m + 1) := by rw [pow_add]; ring
        _ ≤ (8 * p * 2 ^ p * (c * (2 * m + 1 + p) ^ k + c)) * 2 ^ (2 * m + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCsize)
        _ ≤ 2 ^ t * 2 ^ (2 * m + 1) := Nat.mul_le_mul_right _ hsize
        _ = 2 ^ (2 * m + 1) * 2 ^ t := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  -- Step 2 : hence the good set is large
  have hAlarge : 2 ^ (2 * m + 1) ≤ A.card + p * Bad.card := by
    have hsub : (univ \ A).card ≤ p * Bad.card := by
      have h1 : (univ \ A) ⊆ (range p).biUnion (fun r =>
          univ.filter (fun x : Fin (2 * m + 1) → Bool =>
            P (Fin.append x (pad p r))
              ≠ ind (Fq q) (ModFun p (2 * m + 1 + p) (Fin.append x (pad p r))))) := by
        intro x hx
        rw [mem_sdiff, hA] at hx
        obtain ⟨-, hx2⟩ := hx
        rw [mem_filter] at hx2
        push_neg at hx2
        obtain ⟨r, hr, hrx⟩ := hx2 (Finset.mem_univ x)
        exact mem_biUnion.2 ⟨r, hr, by simp [hrx]⟩
      have h2 : ∀ r ∈ range p, (univ.filter (fun x : Fin (2 * m + 1) → Bool =>
          P (Fin.append x (pad p r))
            ≠ ind (Fq q) (ModFun p (2 * m + 1 + p) (Fin.append x (pad p r))))).card
            ≤ Bad.card := by
        intro r _
        refine Finset.card_le_card_of_injOn (fun x => Fin.append x (pad p r)) ?_ ?_
        · intro x hx
          rw [mem_coe, mem_filter] at hx
          rw [mem_coe, hBad, mem_filter]
          exact ⟨Finset.mem_univ _, by rw [hCeval]; exact hx.2⟩
        · intro a _ b _ hab
          funext j
          have hj := congrFun hab (Fin.castAdd p j)
          simpa [Fin.append_left] using hj
      calc (univ \ A).card ≤ _ := Finset.card_le_card h1
        _ ≤ ∑ r ∈ range p, (univ.filter (fun x : Fin (2 * m + 1) → Bool =>
              P (Fin.append x (pad p r))
                ≠ ind (Fq q) (ModFun p (2 * m + 1 + p) (Fin.append x (pad p r))))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _r ∈ range p, Bad.card := Finset.sum_le_sum h2
        _ = p * Bad.card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hcard : (univ \ A).card + A.card = 2 ^ (2 * m + 1) := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)]
      simp
    omega
  -- Step 3 : the function `ζ ^ popcount` has low degree on `A`
  set hfun : (Fin (2 * m + 1) → Bool) → Fq q :=
    ∑ r ∈ range p, (ζ ^ r)⁻¹ • (fun x => 1 - P (Fin.append x (pad p r))) with hhfun
  have hhdeg : hfun ∈ Deg (Fq q) (2 * m + 1) D := by
    rw [hhfun]
    refine Submodule.sum_mem _ (fun r _ => Submodule.smul_mem _ _ ?_)
    have h1 : (fun x : Fin (2 * m + 1) → Bool => 1 - P (Fin.append x (pad p r)))
        = (fun _ => (1 : Fq q)) - (fun x => P (Fin.append x (pad p r))) := rfl
    rw [h1]
    exact Submodule.sub_mem _ (Deg_const_mem 1) (Deg_subst hPD (pad p r))
  have hhA : ∀ x ∈ A, hfun x = ymono ζ univ x := by
    intro x hx
    rw [hA, mem_filter] at hx
    have hx2 := hx.2
    rw [ymono_apply_univ]
    have hterm : ∀ r ∈ range p,
        ((ζ ^ r)⁻¹ • (fun x : Fin (2 * m + 1) → Bool => 1 - P (Fin.append x (pad p r)))) x
          = (ζ ^ r)⁻¹ * (if p ∣ popc x + r then (1 : Fq q) else 0) := by
      intro r hr
      rw [mem_range] at hr
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      rw [hx2 r (mem_range.2 hr)]
      have hpc : popc (Fin.append x (pad p r)) = popc x + r := by
        rw [popc_append, popc_pad (le_of_lt hr)]
      simp only [ModFun, hpc, ind]
      by_cases hdvd : p ∣ popc x + r <;> simp [hdvd]
    rw [hhfun, Finset.sum_apply, Finset.sum_congr rfl hterm]
    obtain ⟨r₀, hr₀lt, hr₀dvd, hr₀uniq⟩ := exists_unique_shift p (popc x)
    rw [Finset.sum_eq_single r₀]
    · rw [if_pos hr₀dvd, mul_one]
      obtain ⟨j, hj⟩ := hr₀dvd
      have hone : ζ ^ (popc x) * ζ ^ r₀ = 1 := by
        rw [← pow_add, hj, pow_mul, hζp, one_pow]
      exact inv_eq_of_mul_eq_one_left hone
    · intro r hr hne
      rw [mem_range] at hr
      have : ¬ p ∣ popc x + r := fun hd => hne (hr₀uniq r hr hd)
      rw [if_neg this, mul_zero]
    · intro h
      exact absurd (mem_range.2 hr₀lt) h
  -- Step 4 : Smolensky's counting bound
  have hcount : A.card ≤ ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i :=
    smolensky_counting ζ hζ0 hζ1 hfun hhdeg hhA
  have hcount2 : A.card ≤ 4 ^ m + D * ((2 * m + 1).choose m) :=
    le_trans hcount (sum_choose_tail_le m D)
  have hDC : 4 * (D * ((2 * m + 1).choose m)) ≤ 2 ^ (2 * m + 1) := by
    rw [← mul_assoc]
    exact four_mul_choose_le (2 * m + 1) m D (by omega)
  have hpow : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [hpow] at hbadsmall hAlarge hDC
  have h4m : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  omega

end CS

