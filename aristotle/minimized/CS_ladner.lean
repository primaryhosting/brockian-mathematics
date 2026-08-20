import Mathlib
/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Ladner's theorem

If `P ≠ NP`, then there is an `NP`-intermediate language: a language in `NP` that is
neither in `P` nor `NP`-complete.

Mathlib has no development of computational complexity, so the ambient complexity-theoretic
setting is packaged into the structure `CS.Model` below: it fixes the classes `P` and `NP`
(as sets of languages, a language being a set of natural numbers viewed as encoded strings),
a length function, an effective enumeration `dec` of the polynomial-time decision procedures
and an effective enumeration `red` of the polynomial-time functions (used to define
polynomial-time many-one reducibility), together with the standard closure properties of
these classes.

Everything in the proof of `CS.ladner` — the delayed-diagonalization construction
(`CS.Model.stage`, defined by well-founded recursion) and all its properties — is carried out
from these data.  The one remaining machine-model fact is supplied as the explicit hypothesis
`hstage` of `CS.ladner`: the "hole" set `{x | Even (stage L (len x))}` determined by the stage
function lies in `P`.  This is the routine clock/bookkeeping part of Ladner's argument: the
witness search performed at stage `n` only inspects inputs of length at most `log₂ log₂ n`
(see `CS.Model.Wit`), so the values `stage L 0, …, stage L n` can be tabulated in time
polynomial in `n`.
-/

namespace CS

open scoped Classical

/-- A language is a set of (encoded) inputs. -/
abbrev Lang : Type := Set ℕ

/-- The complexity-theoretic data the argument runs on: the classes `P` and `NP`, a length
function on encoded inputs, effective enumerations of polynomial-time deciders and of
polynomial-time functions, and the standard closure properties. -/
structure Model where
  /-- The class `P`. -/
  P : Set Lang
  /-- The class `NP`. -/
  NP : Set Lang
  /-- Length of an encoded input. -/
  len : ℕ → ℕ
  /-- `dec i` is the decision procedure of the `i`-th polynomial-time machine. -/
  dec : ℕ → ℕ → Bool
  /-- `red i` is the `i`-th polynomial-time computable function. -/
  red : ℕ → ℕ → ℕ
  /-- There are only finitely many inputs of any given length. -/
  len_finite : ∀ t : ℕ, {x : ℕ | len x ≤ t}.Finite
  /-- `P` is exactly the class of languages decided by the enumerated machines. -/
  P_eq : ∀ A : Lang, A ∈ P ↔ ∃ i, ∀ x, x ∈ A ↔ dec i x = true
  /-- `P ⊆ NP`. -/
  P_subset_NP : P ⊆ NP
  /-- `NP` is closed under intersection with languages in `P`. -/
  NP_inter_P : ∀ A ∈ NP, ∀ B ∈ P, A ∩ B ∈ NP
  /-- Finite languages are in `P`. -/
  P_of_finite : ∀ A : Lang, A.Finite → A ∈ P
  /-- `P` is closed under finite variation. -/
  P_of_finite_symmDiff : ∀ A ∈ P, ∀ B : Lang, {x | ¬ (x ∈ A ↔ x ∈ B)}.Finite → B ∈ P
  /-- `P` is closed downwards under polynomial-time many-one reductions. -/
  P_red_closed : ∀ A B : Lang, (∃ i, ∀ x, x ∈ A ↔ red i x ∈ B) → B ∈ P → A ∈ P
  /-- Polynomial-time functions have polynomially bounded output length. -/
  red_poly : ∀ i, ∃ c, ∀ x, len (red i x) ≤ c * (len x + 1) ^ c

namespace Model

variable (M : Model)

/-- Polynomial-time many-one reducibility `A ≤ₚ B`. -/

def Red (A B : Lang) : Prop := ∃ i, ∀ x, x ∈ A ↔ M.red i x ∈ B

/-- `A` is `NP`-complete: it lies in `NP` and every `NP` language reduces to it. -/

def NPComplete (A : Lang) : Prop := A ∈ M.NP ∧ ∀ B ∈ M.NP, M.Red B A

/-- `A` is `NP`-intermediate: in `NP`, not in `P`, and not `NP`-complete. -/

def NPIntermediate (A : Lang) : Prop := A ∈ M.NP ∧ A ∉ M.P ∧ ¬ M.NPComplete A

end Model

/-- `llog n = log₂ (log₂ n)`. -/

def llog (n : ℕ) : ℕ := Nat.log 2 (Nat.log 2 n)

lemma llog_le_self (n : ℕ) : llog n ≤ n :=
  le_trans (Nat.log_le_self 2 _) (Nat.log_le_self 2 n)

lemma llog_mono : Monotone llog := fun _ _ h =>
  Nat.log_mono_right (Nat.log_mono_right h)

lemma llog_unbounded (t : ℕ) : ∃ n, t ≤ llog n := by
  refine ⟨2 ^ 2 ^ t, ?_⟩
  have h1 : Nat.log 2 (2 ^ 2 ^ t) = 2 ^ t := Nat.log_pow (by norm_num) _
  simp [llog, h1, Nat.log_pow]

namespace Model

variable (M : Model)

/-- Requirement `k` is violated at the input `x`, where membership in the diagonal language
is computed using the (partial) stage function `F`.

Even requirements `k = 2 i` say that the `i`-th polynomial-time machine does not decide the
diagonal language; odd requirements `k = 2 i + 1` say that the `i`-th polynomial-time function
is not a reduction of `L` to the diagonal language. -/

def Mism (L : Lang) (F : ℕ → ℕ) (k x : ℕ) : Prop :=
  if k % 2 = 0 then
    ¬ ((x ∈ L ∧ Even (F (M.len x))) ↔ M.dec (k / 2) x = true)
  else
    ¬ ((x ∈ L) ↔ (M.red (k / 2) x ∈ L ∧ Even (F (M.len (M.red (k / 2) x)))))

/-- Requirement `k` has a witness found by stage `n`: the search only inspects inputs `x`
of length at most `llog n` whose image under the relevant reduction also has length at most
`llog n`. -/

def Wit (L : Lang) (F : ℕ → ℕ) (k n : ℕ) : Prop :=
  ∃ x, M.len x ≤ llog n ∧ M.len (M.red (k / 2) x) ≤ llog n ∧ M.Mism L F k x

/-- The stage function of the delayed diagonalization: `stage L n` is the number of
requirements that have been satisfied by stage `n`. -/

noncomputable def stage (L : Lang) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      if M.Wit L (fun m => if _h : m ≤ n then stage L m else 0) (stage L n) n then
        stage L n + 1
      else stage L n

lemma stage_zero (L : Lang) : M.stage L 0 = 0 := by
  simp [stage]

lemma stage_succ (L : Lang) (n : ℕ) :
    M.stage L (n + 1) =
      if M.Wit L (fun m => if _h : m ≤ n then M.stage L m else 0) (M.stage L n) n then
        M.stage L n + 1
      else M.stage L n := by
  rw [stage]

lemma stage_le_succ (L : Lang) (n : ℕ) : M.stage L n ≤ M.stage L (n + 1) := by
  rw [stage_succ]; split <;> omega

lemma stage_succ_le (L : Lang) (n : ℕ) : M.stage L (n + 1) ≤ M.stage L n + 1 := by
  rw [stage_succ]; split <;> omega

lemma stage_mono (L : Lang) : Monotone (M.stage L) :=
  monotone_nat_of_le_succ (M.stage_le_succ L)

/-- The value of `Mism` only depends on the values of `F` at the lengths of `x` and of its
image under the reduction. -/

lemma mism_congr (L : Lang) (F G : ℕ → ℕ) (k x : ℕ)
    (h1 : F (M.len x) = G (M.len x))
    (h2 : F (M.len (M.red (k / 2) x)) = G (M.len (M.red (k / 2) x))) :
    M.Mism L F k x ↔ M.Mism L G k x := by
  unfold Mism
  split <;> simp only [h1, h2]

/-- If the stage counter increases at `n`, then requirement `stage L n` genuinely fails,
witnessed by some input. -/

lemma mism_of_progress (L : Lang) (n : ℕ)
    (h : M.stage L (n + 1) = M.stage L n + 1) :
    ∃ x, M.Mism L (M.stage L) (M.stage L n) x := by
  rw [stage_succ] at h
  split at h
  · rename_i hw
    obtain ⟨x, hx1, hx2, hx3⟩ := hw
    refine ⟨x, ?_⟩
    have hxn : M.len x ≤ n := le_trans hx1 (llog_le_self n)
    have hrn : M.len (M.red (M.stage L n / 2) x) ≤ n := le_trans hx2 (llog_le_self n)
    rw [M.mism_congr L _ (M.stage L) _ x (by simp [hxn]) (by simp [hrn])] at hx3
    exact hx3
  · omega

/-- If the stage counter does not increase at `n`, then no short input witnesses the
current requirement. -/

lemma not_mism_of_no_progress (L : Lang) (n : ℕ)
    (h : M.stage L (n + 1) = M.stage L n) :
    ∀ x, M.len x ≤ llog n → M.len (M.red (M.stage L n / 2) x) ≤ llog n →
      ¬ M.Mism L (M.stage L) (M.stage L n) x := by
  intro x hx1 hx2 hmis
  rw [stage_succ] at h
  split at h
  · omega
  · rename_i hw
    refine hw ⟨x, hx1, hx2, ?_⟩
    have hxn : M.len x ≤ n := le_trans hx1 (llog_le_self n)
    have hrn : M.len (M.red (M.stage L n / 2) x) ≤ n := le_trans hx2 (llog_le_self n)
    rw [M.mism_congr L _ (M.stage L) _ x (by simp [hxn]) (by simp [hrn])]
    exact hmis

end Model

/-- **Ladner's theorem.**  In the complexity-theoretic setting given by `M`, if `P ≠ NP`
then there is an `NP`-intermediate language: a language in `NP` which is neither in `P`
nor `NP`-complete. -/

theorem ladner (M : Model)
    (hstage : ∀ L : Lang, L ∈ M.NP → {x | Even (M.stage L (M.len x))} ∈ M.P)
    (hPNP : M.P ≠ M.NP) :
    ∃ A : Lang, M.NPIntermediate A := by
  -- Pick a language in `NP \ P`.
  obtain ⟨L, hLNP, hLP⟩ : ∃ L, L ∈ M.NP ∧ L ∉ M.P := by
    by_contra hcon
    push_neg at hcon
    exact hPNP (Set.Subset.antisymm M.P_subset_NP hcon)
  -- Step 1: the stage function is unbounded.
  have hunb : ∀ B : ℕ, ∃ n, B < M.stage L n := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨B, hB⟩ := hcon
    -- the stage function is eventually constant, with value `k`
    have hbdd : BddAbove (Set.range (M.stage L)) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
    have hne : (Set.range (M.stage L)).Nonempty := ⟨M.stage L 0, 0, rfl⟩
    obtain ⟨N, hN⟩ : sSup (Set.range (M.stage L)) ∈ Set.range (M.stage L) :=
      Nat.sSup_mem hne hbdd
    obtain ⟨k, hk⟩ : ∃ k, M.stage L N = k := ⟨_, rfl⟩
    have hconst : ∀ n, N ≤ n → M.stage L n = k := by
      intro n hn
      have h1 : M.stage L N ≤ M.stage L n := M.stage_mono L hn
      have h2 : M.stage L n ≤ sSup (Set.range (M.stage L)) := le_csSup hbdd ⟨n, rfl⟩
      omega
    -- hence requirement `k` is never satisfied
    have hnomis : ∀ x, ¬ M.Mism L (M.stage L) k x := by
      intro x
      obtain ⟨n0, hn0⟩ := llog_unbounded (max (M.len x) (M.len (M.red (k / 2) x)))
      obtain ⟨n, hnmax⟩ : ∃ n, n = max n0 N := ⟨_, rfl⟩
      have hlog : max (M.len x) (M.len (M.red (k / 2) x)) ≤ llog n := by
        rw [hnmax]; exact le_trans hn0 (llog_mono (le_max_left n0 N))
      have hNn : N ≤ n := by rw [hnmax]; exact le_max_right n0 N
      have hfn : M.stage L n = k := hconst n hNn
      have hstep : M.stage L (n + 1) = M.stage L n := by
        rw [hconst (n + 1) (by omega), hfn]
      have h2 := M.not_mism_of_no_progress L n hstep x
      rw [hfn] at h2
      exact h2 (le_trans (le_max_left _ _) hlog) (le_trans (le_max_right _ _) hlog)
    -- both parities lead to `L ∈ P`, a contradiction
    rcases Nat.even_or_odd k with hpar | hpar
    · -- `k` even: the diagonal language is in `P` and differs from `L` on finitely many inputs
      have hpar' : k % 2 = 0 := Nat.even_iff.mp hpar
      have hAP : {x | x ∈ L ∧ Even (M.stage L (M.len x))} ∈ M.P := by
        rw [M.P_eq]
        refine ⟨k / 2, fun x => ?_⟩
        have hx := hnomis x
        unfold Model.Mism at hx
        rw [if_pos hpar'] at hx
        simpa using not_not.mp hx
      refine hLP (M.P_of_finite_symmDiff _ hAP L ?_)
      refine Set.Finite.subset (M.len_finite N) ?_
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      by_contra hlen
      push_neg at hlen
      have hfx : M.stage L (M.len x) = k := hconst _ (le_of_lt hlen)
      exact hx (by simp [hfx, Nat.even_iff.mpr hpar'])
    · -- `k` odd: the diagonal language is finite, hence in `P`, and `L` reduces to it
      have hpar' : ¬ (k % 2 = 0) := by
        have := Nat.odd_iff.mp hpar; omega
      have hred : ∀ x, x ∈ L ↔ M.red (k / 2) x ∈ {x | x ∈ L ∧ Even (M.stage L (M.len x))} := by
        intro x
        have hx := hnomis x
        unfold Model.Mism at hx
        rw [if_neg hpar'] at hx
        simpa using not_not.mp hx
      have hAfin : {x | x ∈ L ∧ Even (M.stage L (M.len x))}.Finite := by
        refine Set.Finite.subset (M.len_finite N) ?_
        intro x hx
        simp only [Set.mem_setOf_eq]
        by_contra hlen
        push_neg at hlen
        have h1 : M.stage L (M.len x) = k := hconst _ (le_of_lt hlen)
        have h2 : Even (M.stage L (M.len x)) := hx.2
        rw [h1] at h2
        have := Nat.even_iff.mp h2
        omega
      exact hLP (M.P_red_closed L _ ⟨k / 2, hred⟩ (M.P_of_finite _ hAfin))
  -- Step 2: every requirement is eventually satisfied.
  have hprog : ∀ k : ℕ, ∃ n, M.stage L n = k ∧ M.stage L (n + 1) = M.stage L n + 1 := by
    intro k
    have hex : ∃ m, k + 1 ≤ M.stage L m := by
      obtain ⟨m, hm⟩ := hunb k; exact ⟨m, hm⟩
    have hmspec : k + 1 ≤ M.stage L (Nat.find hex) := Nat.find_spec hex
    have hm0 : Nat.find hex ≠ 0 := by
      intro h
      rw [h, M.stage_zero L] at hmspec
      omega
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ (k + 1 ≤ M.stage L n) := Nat.find_min hex (by omega)
    rw [hn] at hmspec
    have hle : M.stage L (n + 1) ≤ M.stage L n + 1 := M.stage_succ_le L n
    exact ⟨n, by omega, by omega⟩
  have hreq : ∀ k : ℕ, ∃ x, M.Mism L (M.stage L) k x := by
    intro k
    obtain ⟨n, hn1, hn2⟩ := hprog k
    have h := M.mism_of_progress L n hn2
    rw [hn1] at h
    exact h
  -- Step 3: the diagonal language is `NP`-intermediate.
  refine ⟨{x | x ∈ L ∧ Even (M.stage L (M.len x))}, ?_, ?_, ?_⟩
  · have hinter : {x | x ∈ L ∧ Even (M.stage L (M.len x))}
        = L ∩ {x | Even (M.stage L (M.len x))} := by ext x; simp
    rw [hinter]
    exact M.NP_inter_P L hLNP _ (hstage L hLNP)
  · intro hAP
    obtain ⟨i, hi⟩ := (M.P_eq _).mp hAP
    obtain ⟨x, hx⟩ := hreq (2 * i)
    unfold Model.Mism at hx
    rw [if_pos (by omega : (2 * i) % 2 = 0), (by omega : 2 * i / 2 = i)] at hx
    exact hx (by simpa using hi x)
  · rintro ⟨-, hc⟩
    obtain ⟨i, hi⟩ := hc L hLNP
    obtain ⟨x, hx⟩ := hreq (2 * i + 1)
    unfold Model.Mism at hx
    rw [if_neg (by omega : ¬ ((2 * i + 1) % 2 = 0)), (by omega : (2 * i + 1) / 2 = i)] at hx
    exact hx (by simpa using hi x)

/-!
## Consistency of the axioms

The axioms bundled in `CS.Model` are consistent, and are consistent with `P ≠ NP`: the toy
instance below (where `P` consists of the finite languages and `NP` of the finite languages
together with the full language) satisfies all of them, and separates its two classes.
This rules out the possibility that `CS.ladner` is vacuously true because of contradictory
assumptions on the model.  (Of course the toy instance does not satisfy the hypothesis
`hstage` of `CS.ladner` for any interesting reason; it is only a consistency witness.)
-/

/-- A toy instance of `Model`: `P` is the class of finite languages, and `NP` is the class of
finite languages together with the full language. -/
