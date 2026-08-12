/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 rejects a `/-!` module docstring before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring
-- immediately after the imports.)
import RequestProject.Ramsey

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

/-- A finite set of natural numbers is *relatively large* (in the sense of
Paris–Harrington) if it is nonempty and its cardinality is at least its least
element. -/
def IsLarge (H : Finset ℕ) : Prop :=
  ∃ a ∈ H, (∀ b ∈ H, a ≤ b) ∧ a ≤ H.card

/-- `IsLarge` is exactly the Paris–Harrington largeness condition: a nonempty set
is large iff its least element is at most its cardinality. -/
theorem isLarge_iff_min' {H : Finset ℕ} (h : H.Nonempty) :
    IsLarge H ↔ H.min' h ≤ H.card := by
  constructor
  · rintro ⟨a, haH, -, hcard⟩
    exact le_trans (H.min'_le a haH) hcard
  · intro hle
    exact ⟨H.min' h, H.min'_mem h, fun b hb => H.min'_le b hb, hle⟩

/-- `IsHomogeneous n c H` says that the colouring `c` of `n`-element sets takes the
same value on all `n`-element subsets of the finite set `H`. -/
def IsHomogeneous (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (H : Finset ℕ) : Prop :=
  ∀ s ⊆ H, ∀ t ⊆ H, s.card = n → t.card = n → c s = c t

/-- **The strengthened finite Ramsey theorem (Paris–Harrington)**.

For all `n, k, m` there is an `N` such that for every colouring `c` of the
`n`-element subsets of `{1, …, N}` with `k` colours there is a subset
`H ⊆ {1, …, N}` which is homogeneous for `c`, has at least `m` elements, and is
*relatively large*: its cardinality is at least its least element.

(The second half of the Paris–Harrington result — that this statement is not
provable in first-order Peano Arithmetic — is a metamathematical statement about
a formal theory and is not formalized here; what is proved here is the
mathematical content, namely that the statement is true.) -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ H ⊆ Finset.Icc 1 N, m ≤ H.card ∧ IsLarge H ∧ IsHomogeneous n c H := by
  by_contra hcon
  -- If the theorem fails, there are "bad" colourings `cf N` for every `N`.
  have hbad : ∀ N : ℕ, ∃ c : Finset ℕ → Fin k, ∀ H : Finset ℕ, H ⊆ Finset.Icc 1 N →
      m ≤ H.card → IsLarge H → ¬ IsHomogeneous n c H := by
    intro N
    by_contra h
    push_neg at h
    exact hcon ⟨N, fun c => by
      obtain ⟨H, h1, h2, h3, h4⟩ := h c
      exact ⟨H, h1, h2, h3, h4⟩⟩
  choose cf hcf using hbad
  -- A limit colouring obtained from a nonprincipal ultrafilter.
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hUle : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le Filter.atTop
  have hlim : ∀ s : Finset ℕ, ∃ j : Fin k, ∀ᶠ N in (U : Filter ℕ), cf N s = j := by
    intro s
    have h0 : ∀ᶠ N in (U : Filter ℕ), ∃ j : Fin k, cf N s = j :=
      Filter.Eventually.of_forall fun N => ⟨cf N s, rfl⟩
    exact Ultrafilter.eventually_exists_iff.mp h0
  choose c hc using hlim
  -- Infinite Ramsey applied to the limit colouring.
  obtain ⟨A, hAsub, hAinf, hAhom⟩ :=
    Frontier.infinite_ramsey n c (Set.Ici 1) (Set.Ici_infinite 1)
  obtain ⟨a, haA⟩ := hAinf.nonempty
  have ha1 : 1 ≤ a := hAsub haA
  -- a large homogeneous set for the limit colouring
  have hAa : (A ∩ Set.Ioi a).Infinite := by
    refine Set.Infinite.mono ?_ (hAinf.diff (Set.finite_Iic a))
    intro x hx
    exact ⟨hx.1, by simpa using hx.2⟩
  set t : ℕ := max m a with ht_def
  obtain ⟨H₀, hH₀sub, hH₀card⟩ := hAa.exists_subset_card_eq (t - 1)
  have haH₀ : a ∉ H₀ := by
    intro h
    have := (hH₀sub (by exact_mod_cast h)).2
    simp only [Set.mem_Ioi] at this
    omega
  set H : Finset ℕ := insert a H₀ with hH_def
  have hHcard : H.card = t := by
    rw [hH_def, Finset.card_insert_of_notMem haH₀, hH₀card]
    have : 1 ≤ t := le_trans ha1 (le_max_right m a)
    omega
  have hHA : (↑H : Set ℕ) ⊆ A := by
    intro x hx
    rw [hH_def] at hx
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
    rcases hx with rfl | hx
    · exact haA
    · exact (hH₀sub (by exact_mod_cast hx)).1
  have hHmin : ∀ b ∈ H, a ≤ b := by
    intro b hb
    rw [hH_def] at hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · exact le_of_lt (hH₀sub (by exact_mod_cast hb)).2
  have haH : a ∈ H := by rw [hH_def]; exact Finset.mem_insert_self _ _
  have hlarge : IsLarge H := ⟨a, haH, hHmin, by rw [hHcard]; exact le_max_right m a⟩
  have hmH : m ≤ H.card := by rw [hHcard]; exact le_max_left m a
  -- choose a level `M` of the ultrafilter at which `cf M` agrees with the limit
  -- colouring on all `n`-subsets of `H`, and which is large enough to contain `H`.
  set B : ℕ := H.sup id with hB_def
  have hgood : (⋂ s ∈ (↑(H.powersetCard n) : Set (Finset ℕ)), {N : ℕ | cf N s = c s}) ∩
      {N : ℕ | B ≤ N} ∈ (U : Filter ℕ) := by
    refine Filter.inter_mem ?_ ?_
    · refine (Filter.biInter_mem (H.powersetCard n).finite_toSet).mpr ?_
      intro s _
      exact hc s
    · exact hUle (Filter.mem_atTop B)
  obtain ⟨M, hM1, hM2⟩ := Filter.nonempty_of_mem hgood
  have hMB : B ≤ M := hM2
  have hHIcc : H ⊆ Finset.Icc 1 M := by
    intro x hx
    have hx1 : 1 ≤ x := hAsub (hHA (by exact_mod_cast hx))
    have hxB : x ≤ B := Finset.le_sup (f := id) hx
    exact Finset.mem_Icc.mpr ⟨hx1, le_trans hxB hMB⟩
  refine hcf M H hHIcc hmH hlarge ?_
  intro s hs u hu hsc huc
  have hs' : cf M s = c s := by
    have := Set.mem_iInter₂.mp hM1 s (by simpa using Finset.mem_powersetCard.mpr ⟨hs, hsc⟩)
    exact this
  have hu' : cf M u = c u := by
    have := Set.mem_iInter₂.mp hM1 u (by simpa using Finset.mem_powersetCard.mpr ⟨hu, huc⟩)
    exact this
  have : c s = c u :=
    hAhom s u (fun x hx => hHA (hs (by exact_mod_cast hx)))
      (fun x hx => hHA (hu (by exact_mod_cast hx))) hsc huc
  rw [hs', hu', this]

/-- The ordinary finite Ramsey theorem, as an immediate consequence of the
strengthened (Paris–Harrington) version. -/
theorem finite_ramsey (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k,
      ∃ H ⊆ Finset.Icc 1 N, m ≤ H.card ∧ IsHomogeneous n c H := by
  obtain ⟨N, hN⟩ := Paris_Harrington n k m
  refine ⟨N, fun c => ?_⟩
  obtain ⟨H, h1, h2, -, h4⟩ := hN c
  exact ⟨H, h1, h2, h4⟩

end Frontier

/-
Infinite Ramsey theorem for colourings of `n`-element subsets of `ℕ`.

This file is auxiliary infrastructure for the Paris–Harrington theorem; Mathlib
does not contain Ramsey's theorem, so we develop it here.
-/
import Mathlib

namespace Frontier

/-- `HomogOn n c A` says that the colouring `c` is constant on the `n`-element
subsets of `A`. -/
def HomogOn (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (A : Set ℕ) : Prop :=
  ∀ s t : Finset ℕ, (↑s : Set ℕ) ⊆ A → (↑t : Set ℕ) ⊆ A → s.card = n → t.card = n → c s = c t

/-- One step of the construction in the proof of the infinite Ramsey theorem:
given an infinite set `T`, we find `a ∈ T` and an infinite `T' ⊆ T` consisting of
elements above `a` such that `c (insert a ·)` is constant on `n`-subsets of `T'`. -/
theorem step_exists {k n : ℕ}
    (IH : ∀ (c : Finset ℕ → Fin k) (S : Set ℕ), S.Infinite →
      ∃ A ⊆ S, A.Infinite ∧ HomogOn n c A)
    (c : Finset ℕ → Fin k) (T : Set ℕ) (hT : T.Infinite) :
    ∃ (a : ℕ) (T' : Set ℕ) (j : Fin k), a ∈ T ∧ T' ⊆ T ∧ T'.Infinite ∧
      (∀ x ∈ T', a < x) ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ T' → s.card = n → c (insert a s) = j := by
  obtain ⟨a, ha⟩ := hT.nonempty
  have hTa : (T ∩ Set.Ioi a).Infinite := by
    refine Set.Infinite.mono ?_ (hT.diff (Set.finite_Iic a))
    intro x hx
    exact ⟨hx.1, by simpa using hx.2⟩
  obtain ⟨A, hAsub, hAinf, hAhom⟩ := IH (fun s => c (insert a s)) (T ∩ Set.Ioi a) hTa
  obtain ⟨s₀, hs₀sub, hs₀card⟩ := hAinf.exists_subset_card_eq n
  refine ⟨a, A, c (insert a s₀), ha, fun x hx => (hAsub hx).1, hAinf,
    fun x hx => (hAsub hx).2, ?_⟩
  intro s hs hcard
  exact hAhom s s₀ hs hs₀sub hcard hs₀card

/-- **Infinite Ramsey theorem**: any colouring of the `n`-element subsets of `ℕ`
with `k` colours is constant on the `n`-element subsets of some infinite subset of
any given infinite set. -/
theorem infinite_ramsey {k : ℕ} (n : ℕ) (c : Finset ℕ → Fin k) (S : Set ℕ)
    (hS : S.Infinite) : ∃ A ⊆ S, A.Infinite ∧ HomogOn n c A := by
  induction n generalizing c S with
  | zero =>
      refine ⟨S, subset_rfl, hS, ?_⟩
      intro s t _ _ hs ht
      rw [Finset.card_eq_zero] at hs ht
      subst hs; subst ht; rfl
  | succ n IH =>
      have key : ∀ TT : {T : Set ℕ // T.Infinite},
          ∃ p : ℕ × {T : Set ℕ // T.Infinite} × Fin k,
            p.1 ∈ TT.1 ∧ (p.2.1 : Set ℕ) ⊆ TT.1 ∧ (∀ x ∈ (p.2.1 : Set ℕ), p.1 < x) ∧
            ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ (p.2.1 : Set ℕ) → s.card = n →
              c (insert p.1 s) = p.2.2 := by
        intro TT
        obtain ⟨a, T', j, ha, hsub, hinf, hgt, hcol⟩ :=
          step_exists (fun c' S' hS' => IH c' S' hS') c TT.1 TT.2
        exact ⟨⟨a, ⟨T', hinf⟩, j⟩, ha, hsub, hgt, hcol⟩
      choose F hF1 hF2 hF3 hF4 using key
      -- the sequence of nested infinite sets
      let seq : ℕ → {T : Set ℕ // T.Infinite} := fun i =>
        Nat.rec (⟨S, hS⟩ : {T : Set ℕ // T.Infinite}) (fun _ TT => (F TT).2.1) i
      let a : ℕ → ℕ := fun i => (F (seq i)).1
      let d : ℕ → Fin k := fun i => (F (seq i)).2.2
      have hmem : ∀ i, a i ∈ (seq i).1 := fun i => hF1 (seq i)
      have hstep : ∀ i, ((seq (i+1)).1) ⊆ (seq i).1 := fun i => hF2 (seq i)
      have hgt : ∀ i, ∀ x ∈ (seq (i+1)).1, a i < x := fun i => hF3 (seq i)
      have hcol : ∀ i, ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ (seq (i+1)).1 → s.card = n →
          c (insert (a i) s) = d i := fun i => hF4 (seq i)
      have hmono : ∀ i j : ℕ, i ≤ j → ((seq j).1) ⊆ (seq i).1 := by
        intro i j hij
        induction hij with
        | refl => exact subset_rfl
        | step h ih => exact (hstep _).trans ih
      have hlt : ∀ i, a i < a (i + 1) := fun i => hgt i _ (hmem (i + 1))
      have hsm : StrictMono a := strictMono_nat_of_lt_succ hlt
      -- pigeonhole on the colours
      obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber d
      have hjinf : (d ⁻¹' {j}).Infinite := Set.infinite_coe_iff.mp hj
      refine ⟨a '' (d ⁻¹' {j}), ?_, ?_, ?_⟩
      · rintro x ⟨i, -, rfl⟩
        exact hmono 0 i (Nat.zero_le i) (hmem i)
      · exact hjinf.image (hsm.injective.injOn)
      · -- every `(n+1)`-subset gets colour `j`
        have main : ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ a '' (d ⁻¹' {j}) → s.card = n + 1 →
            c s = j := by
          intro s hs hcard
          have hne : s.Nonempty := Finset.card_pos.mp (by omega)
          set x := s.min' hne with hx_def
          have hxs : x ∈ s := s.min'_mem hne
          obtain ⟨i, hi, hix⟩ := hs (by exact_mod_cast hxs)
          have hi' : d i = j := hi
          have hsub : (↑(s.erase x) : Set ℕ) ⊆ (seq (i+1)).1 := by
            intro y hy
            simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe,
              Set.mem_singleton_iff] at hy
            obtain ⟨hys, hyx⟩ := hy
            obtain ⟨i', hi'mem, hi'x⟩ := hs (by exact_mod_cast hys)
            have hxy : x < y := lt_of_le_of_ne (s.min'_le y hys) (Ne.symm hyx)
            have : i < i' := by
              by_contra hcon
              have : i' ≤ i := Nat.le_of_not_lt hcon
              have := hsm.monotone this
              rw [hi'x, hix] at this
              omega
            have h1 : a i' ∈ (seq i').1 := hmem i'
            have := hmono (i + 1) i' this h1
            rwa [hi'x] at this
          have hcard' : (s.erase x).card = n := by
            rw [Finset.card_erase_of_mem hxs, hcard]
            omega
          have := hcol i (s.erase x) hsub hcard'
          rw [hi'] at this
          rwa [hix, Finset.insert_erase hxs] at this
        intro s t hs ht hsc htc
        rw [main s hs hsc, main t ht htc]

end Frontier

