import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Remarks on the development

Mathlib (as of this toolchain) contains no Ramsey-type theorem: neither the finite nor
the infinite Ramsey theorem is available, so both are developed here from scratch.
The Mathlib ingredients used are the ultrafilter API
(`Ultrafilter.of`, `Ultrafilter.of_le`, `Ultrafilter.eventually_exists_iff`),
the infinite pigeonhole principle `Finite.exists_infinite_fiber`,
and `Set.Infinite.exists_subset_card_eq`.

The development proves:
* `Frontier.infinite_ramsey` — the infinite Ramsey theorem for `n`-element subsets
  and `k` colours (proved by induction on `n`);
* `Frontier.Paris_Harrington` — the strengthened finite Ramsey theorem, deduced from
  the infinite version by an ultrafilter compactness argument;
* `Frontier.finite_ramsey` — the ordinary finite Ramsey theorem, as a corollary.

The assertion that `Frontier.Paris_Harrington` is *unprovable in Peano Arithmetic* is a
statement about a formal proof system rather than a mathematical statement about the
naturals, and is not formalised here.
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A set `T` of naturals is *homogeneous* of colour `α` for the colouring `c` of
`n`-element subsets if every `n`-element subset of `T` gets colour `α`. -/
def Homog (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (T : Set ℕ) (α : Fin k) : Prop :=
  ∀ s : Finset ℕ, ↑s ⊆ T → s.card = n → c s = α

/-- A finite set of naturals is *relatively large* (in the sense of Paris–Harrington)
if it is nonempty and its cardinality is at least its least element. -/
def IsLarge (H : Finset ℕ) : Prop := ∃ a ∈ H, (∀ y ∈ H, a ≤ y) ∧ a ≤ H.card

/-! ### The infinite Ramsey theorem -/

/-- The elements of `S` above its least element. -/
def nxt (S : Set ℕ) : Set ℕ := {x ∈ S | sInf S < x}

lemma nxt_subset (S : Set ℕ) : nxt S ⊆ S := fun _ hx => hx.1

lemma nxt_infinite {S : Set ℕ} (hS : S.Infinite) : (nxt S).Infinite := by
  have hsub : S \ Set.Iic (sInf S) ⊆ nxt S := fun x hx => ⟨hx.1, by simpa using hx.2⟩
  exact (hS.diff (Set.finite_Iic _)).mono hsub

/-- The inductive step of the infinite Ramsey theorem. -/
lemma ramsey_step (n k : ℕ)
    (IH : ∀ (c : Finset ℕ → Fin k) (S : Set ℕ), ∃ (T : Set ℕ) (α : Fin k),
      S.Infinite → (T ⊆ S ∧ T.Infinite ∧ Homog n c T α))
    (c : Finset ℕ → Fin k) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ α, Homog (n + 1) c T α := by
  choose F col hF using IH
  set g : Set ℕ → Set ℕ := fun X => F (fun s => c (insert (sInf X) s)) (nxt X)
  set A : ℕ → Set ℕ := fun i => g^[i] S with hAdef
  have hAsucc : ∀ i, A (i + 1) = g (A i) := by
    intro i
    simp [hAdef, Function.iterate_succ_apply']
  have hAinf : ∀ i, (A i).Infinite := by
    intro i
    induction i with
    | zero => exact hS
    | succ i ih =>
      rw [hAsucc]
      exact (hF _ _ (nxt_infinite ih)).2.1
  have hstep : ∀ i, A (i + 1) ⊆ nxt (A i) := by
    intro i
    rw [hAsucc]
    exact (hF _ _ (nxt_infinite (hAinf i))).1
  set al : ℕ → Fin k := fun i => col (fun s => c (insert (sInf (A i)) s)) (nxt (A i))
  have hhom : ∀ i, ∀ X : Finset ℕ, ↑X ⊆ A (i + 1) → X.card = n →
      c (insert (sInf (A i)) X) = al i := by
    intro i X hX hcard
    have h := (hF (fun s => c (insert (sInf (A i)) s)) (nxt (A i)) (nxt_infinite (hAinf i))).2.2
    rw [hAsucc] at hX
    exact h X hX hcard
  set a : ℕ → ℕ := fun i => sInf (A i)
  have hamem : ∀ i, a i ∈ A i := fun i => Nat.sInf_mem (hAinf i).nonempty
  have hmono : ∀ i j : ℕ, i ≤ j → A j ⊆ A i := by
    intro i j hij
    induction j with
    | zero =>
      have : i = 0 := Nat.le_zero.mp hij
      simp [this]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact ((hstep j).trans (nxt_subset _)).trans (ih (Nat.lt_succ_iff.mp h))
      · have : i = j + 1 := le_antisymm hij h
        simp [this]
  have halt : StrictMono a := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    exact (hstep i (hamem (i + 1))).2
  obtain ⟨α, hαinf⟩ := Finite.exists_infinite_fiber al
  have hI : (al ⁻¹' {α}).Infinite := Set.infinite_coe_iff.mp hαinf
  refine ⟨a '' (al ⁻¹' {α}), ?_, hI.image (halt.injective.injOn), α, ?_⟩
  · rintro x ⟨i, -, rfl⟩
    exact hmono 0 i (Nat.zero_le _) (hamem i)
  · intro s hs hcard
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    set b := s.min' hne
    have hbs : b ∈ s := s.min'_mem hne
    obtain ⟨i₀, hi₀, hi₀b⟩ := hs hbs
    have hXsub : ↑(s.erase b) ⊆ A (i₀ + 1) := by
      intro y hy
      have hy' : y ∈ s.erase b := hy
      have hys : y ∈ s := Finset.mem_of_mem_erase hy'
      have hyne : y ≠ b := Finset.ne_of_mem_erase hy'
      obtain ⟨j, -, rfl⟩ := hs hys
      have hlt : b < a j := lt_of_le_of_ne (s.min'_le _ hys) (Ne.symm hyne)
      have : i₀ < j := by
        have : a i₀ < a j := by rw [hi₀b]; exact hlt
        exact halt.lt_iff_lt.mp this
      exact hmono (i₀ + 1) j this (hamem j)
    have hXcard : (s.erase b).card = n := by
      rw [Finset.card_erase_of_mem hbs, hcard]
      omega
    have := hhom i₀ (s.erase b) hXsub hXcard
    rw [show sInf (A i₀) = b from hi₀b, Finset.insert_erase hbs] at this
    rw [this]
    exact hi₀

/-- **Infinite Ramsey theorem.** Every `k`-colouring of the `n`-element subsets of an
infinite set `S` of naturals admits an infinite homogeneous subset. -/
theorem infinite_ramsey (n k : ℕ) (c : Finset ℕ → Fin k) (S : Set ℕ) (hS : S.Infinite) :
    ∃ T ⊆ S, T.Infinite ∧ ∃ α, Homog n c T α := by
  induction n generalizing c S with
  | zero =>
    refine ⟨S, subset_rfl, hS, c ∅, ?_⟩
    intro s _ hs
    rw [Finset.card_eq_zero] at hs
    subst hs
    rfl
  | succ n ih =>
    refine ramsey_step n k ?_ c S hS
    intro c' S'
    by_cases h : S'.Infinite
    · obtain ⟨T, hT, hTi, α, hα⟩ := ih c' S' h
      exact ⟨T, α, fun _ => ⟨hT, hTi, hα⟩⟩
    · exact ⟨∅, c' ∅, fun h' => absurd h' h⟩

/-! ### The Paris–Harrington principle -/

/-- **The Paris–Harrington strengthened finite Ramsey theorem.**
For all `n, k, m` there is `N` such that for every colouring `c` of the `n`-element
subsets of `{1, …, N}` with `k` colours there is a subset `H ⊆ {1, …, N}` which is
homogeneous for `c`, has at least `m` elements, and is *relatively large*:
its cardinality is at least its least element.

(The second half of the Paris–Harrington theorem — that this statement is not provable
in first-order Peano Arithmetic — is a metamathematical assertion about a formal system
and is not formalised here.) -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ,
      H ⊆ Finset.Icc 1 N ∧ m ≤ H.card ∧ IsLarge H ∧ ∃ α, Homog n c ↑H α := by
  by_contra hcon
  push_neg at hcon
  choose cb hcb using hcon
  -- A nonprincipal ultrafilter on `ℕ`, used to take a limit of the bad colourings.
  set U : Ultrafilter ℕ := Ultrafilter.of (Filter.cofinite : Filter ℕ)
  have hUcof : (U : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  -- The limit colouring.
  have hlim : ∀ s : Finset ℕ, ∃ α : Fin k, ∀ᶠ N in (U : Filter ℕ), cb N s = α := by
    intro s
    have h : ∀ᶠ N in (U : Filter ℕ), ∃ α : Fin k, cb N s = α :=
      Filter.Eventually.of_forall fun N => ⟨cb N s, rfl⟩
    exact Ultrafilter.eventually_exists_iff.mp h
  choose cstar hcstar using hlim
  -- Infinite Ramsey applied to the limit colouring.
  obtain ⟨T, hTS, hTinf, α, hα⟩ :=
    infinite_ramsey n k cstar (Set.Ici 1) (Set.Ici_infinite 1)
  set a := sInf T
  have haT : a ∈ T := Nat.sInf_mem hTinf.nonempty
  have ha1 : 1 ≤ a := hTS haT
  have hamin : ∀ y ∈ T, a ≤ y := fun y hy => Nat.sInf_le hy
  set M := max m a
  have hM1 : 1 ≤ M := le_trans ha1 (le_max_right _ _)
  have hinf' : (T ∩ Set.Ioi a).Infinite := by
    refine (hTinf.diff (Set.finite_Iic a)).mono ?_
    intro x hx
    exact ⟨hx.1, by simpa using hx.2⟩
  obtain ⟨H₀, hH₀sub, hH₀card⟩ := hinf'.exists_subset_card_eq (M - 1)
  set H : Finset ℕ := insert a H₀ with hHdef
  have haH₀ : a ∉ H₀ := fun h => absurd (hH₀sub h).2 (lt_irrefl a)
  have hcard : H.card = M := by
    rw [hHdef, Finset.card_insert_of_notMem haH₀, hH₀card]
    omega
  have hHT : ↑H ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ haT
    · exact (hH₀sub h).1
  have hHmin : ∀ y ∈ H, a ≤ y := fun y hy => hamin y (hHT hy)
  -- Almost every `N` agrees with the limit colouring on subsets of `H`, and is large.
  have hev1 : ∀ᶠ N in (U : Filter ℕ), ∀ s ∈ H.powerset, cb N s = cstar s :=
    (Filter.eventually_all_finset _).2 fun s _ => hcstar s
  have hev2 : ∀ᶠ N in (U : Filter ℕ), ∀ x ∈ H, x ≤ N := by
    have h : ∀ᶠ N in (Filter.cofinite : Filter ℕ), ∀ x ∈ H, x ≤ N := by
      rw [Nat.cofinite_eq_atTop]
      exact Filter.eventually_atTop.2
        ⟨H.sup id, fun N hN x hx => le_trans (Finset.le_sup (f := id) hx) hN⟩
    exact hUcof h
  obtain ⟨N, hN1, hN2⟩ := (hev1.and hev2).exists
  refine hcb N H ?_ ?_ ?_ α ?_
  · intro x hx
    exact Finset.mem_Icc.2 ⟨le_trans ha1 (hHmin x hx), hN2 x hx⟩
  · rw [hcard]; exact le_max_left _ _
  · exact ⟨a, Finset.mem_insert_self _ _, hHmin, by rw [hcard]; exact le_max_right _ _⟩
  · intro s hs hscard
    have hsH : s ∈ H.powerset := Finset.mem_powerset.2 (by exact_mod_cast hs)
    rw [hN1 s hsH]
    exact hα s (fun x hx => hHT (hs hx)) hscard

/-- The ordinary finite Ramsey theorem, an immediate consequence of the
Paris–Harrington principle (one simply forgets the largeness of `H`). -/
theorem finite_ramsey (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ,
      H ⊆ Finset.Icc 1 N ∧ m ≤ H.card ∧ ∃ α, Homog n c ↑H α := by
  obtain ⟨N, hN⟩ := Paris_Harrington n k m
  refine ⟨N, fun c => ?_⟩
  obtain ⟨H, h₁, h₂, -, h₄⟩ := hN c
  exact ⟨H, h₁, h₂, h₄⟩

end Frontier

