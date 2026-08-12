/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module documentation, so the header above is
-- written as a plain comment; it is repeated as the module docstring below.)
import RequestProject.Savitch.Final

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The machine model is the standard off-line random-access model of space bounded computation
(see `RequestProject/Savitch/Model.lean`): the memory of a machine is a bit string, one step
rewrites the memory using the memory content and a single input bit, read at a position which
is determined by the memory, and the space used on an input is the maximal length of a memory
string occurring in the computation.

`NSPACE f` and `DSPACE g` are the classes of languages accepted by nondeterministic,
respectively deterministic, machines running in space `O (f n)`, respectively `O (g n)`.

The proof is Savitch's: for a nondeterministic machine `M` running in space `S` on the input
`x`, deciding whether `M` accepts amounts to deciding reachability in the configuration graph
of `M` on `x`, whose vertices are the words of length at most `S`.  Reachability by a path of
length at most `2 ^ k` is decided by the midpoint recursion `savR`, whose recursion depth is
`k`; taking `k = S + 1` suffices because there are only `2 ^ (S + 1) - 1` configurations.  The
simulator runs this recursion with an explicit stack of at most `S + 2` frames, each holding
three words of length at most `S`, so it uses `O (S ^ 2)` bits.  Since the simulator does not
know `S`, it runs the whole procedure for stages `s = 0, 1, 2, …`, and at each stage also
checks whether some reachable configuration has a successor of length more than `s`; the first
stage at which this check fails gives the correct answer, and this happens at the latest at
stage `S`.
-/

namespace CS

namespace Savitch

/-- A deterministic machine viewed as a nondeterministic machine. -/
def toN (D : DMachine) : NMachine where
  ask := D.ask
  next := fun m bit => [D.next m bit]
  verdict := D.verdict

theorem toN_reach_iff (D : DMachine) (x c : Word) :
    (toN D).Reach x c ↔ ∃ t, D.run x t = c := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail c₁ c₂ _ hstep ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨hv, hmem⟩ := hstep
        refine ⟨t + 1, ?_⟩
        rw [run_succ, ht, if_pos (show D.verdict c₁ = none from hv)]
        simp only [toN, List.mem_singleton] at hmem
        exact hmem.symm
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih =>
        rw [run_succ]
        by_cases hv : D.verdict (D.run x t) = none
        · rw [if_pos hv]
          exact ih.tail ⟨hv, by simp [toN]⟩
        · rw [if_neg hv]
          exact ih

theorem toN_lang (D : DMachine) : (toN D).lang = D.lang := by
  ext x
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨t, rfl⟩ := (toN_reach_iff D x c).1 hc
    exact ⟨t, hv⟩
  · rintro ⟨t, ht⟩
    exact ⟨D.run x t, (toN_reach_iff D x _).2 ⟨t, rfl⟩, ht⟩

theorem toN_space (D : DMachine) (x : Word) (s : ℕ) (h : D.SpaceBoundedOn x s) :
    (toN D).SpaceBoundedOn x s := by
  intro c hc
  obtain ⟨t, rfl⟩ := (toN_reach_iff D x c).1 hc
  exact h t

end Savitch

/-- Deterministic space is contained in nondeterministic space. -/
theorem DSPACE_subset_NSPACE (g : ℕ → ℕ) : DSPACE g ⊆ NSPACE g := by
  rintro L ⟨D, c, hspace, rfl⟩
  exact ⟨Savitch.toN D, c, fun x => Savitch.toN_space D x _ (hspace x), Savitch.toN_lang D⟩

/-- **Savitch's theorem**: every language accepted by a nondeterministic machine in space
`O (f n)` is accepted by a deterministic machine in space `O (f n ^ 2)`. -/
theorem savitch (f : ℕ → ℕ) : NSPACE f ⊆ DSPACE (fun n => f n ^ 2) := by
  rintro L ⟨M, c, hspace, rfl⟩
  refine ⟨Savitch.savitchD M, 75 * (c + 1) ^ 2, ?_, ?_⟩
  · intro x t
    have hbound := Savitch.savitchD_space M x (c * f x.length + c) (hspace x) t
    refine le_trans hbound ?_
    set F := f x.length with hF
    have h1 : c * F + c + 1 ≤ (c + 1) * (F + 1) := by nlinarith
    have h2 : (c * F + c + 1) ^ 2 ≤ ((c + 1) * (F + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (F + 1) ^ 2 ≤ 3 * F ^ 2 + 3 := by
      cases F with
      | zero => norm_num
      | succ n => nlinarith
    calc 25 * (c * F + c + 1) ^ 2 ≤ 25 * ((c + 1) * (F + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ h2
      _ = 25 * (c + 1) ^ 2 * (F + 1) ^ 2 := by ring
      _ ≤ 25 * (c + 1) ^ 2 * (3 * F ^ 2 + 3) := Nat.mul_le_mul_left _ h3
      _ = 75 * (c + 1) ^ 2 * F ^ 2 + 75 * (c + 1) ^ 2 := by ring
  · ext x
    exact Savitch.savitchD_lang M x (c * f x.length + c) (hspace x)

/-- Savitch's theorem for polynomial space: `PSPACE = NPSPACE`. -/
theorem pspace_eq_npspace : PSPACE = NPSPACE := by
  ext L
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, DSPACE_subset_NSPACE _ hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨2 * k, ?_⟩
    have h := savitch (fun n => n ^ k) hk
    have heq : (fun n : ℕ => (n ^ k) ^ 2) = fun n : ℕ => n ^ (2 * k) := by
      funext n
      rw [← pow_mul, Nat.mul_comm]
    rwa [heq] at h

/-! ## A sanity check

The classes are not degenerate: here is a concrete non-trivial language in `DSPACE`, decided by
a machine which reads a single input bit. -/

namespace Savitch

/-- A deterministic machine which reads the first input bit and accepts iff it is `true`. -/
def firstBitD : DMachine where
  ask := fun _ => 0
  next := fun _ bit => if bit = some true then [true] else [false]
  verdict := fun m =>
    match m with
    | [] => none
    | b :: _ => some b

theorem firstBitD_run_succ (x : Word) (t : ℕ) :
    firstBitD.run x (t + 1) = if x[0]? = some true then [true] else [false] := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [run_succ, ih]
      by_cases h : x[0]? = some true <;> simp [h, firstBitD]

end Savitch

/-- The language of words whose first bit is `true` is decided in constant space. -/
theorem firstBit_mem_DSPACE :
    {x : Word | x[0]? = some true} ∈ DSPACE (fun _ => 1) := by
  refine ⟨Savitch.firstBitD, 1, ?_, ?_⟩
  · intro x t
    cases t with
    | zero => simp [DMachine.run]
    | succ t =>
        rw [Savitch.firstBitD_run_succ]
        by_cases h : x[0]? = some true <;> simp [h]
  · ext x
    simp only [DMachine.lang, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | zero => simp [DMachine.run, Savitch.firstBitD] at ht
      | succ t =>
          rw [Savitch.firstBitD_run_succ] at ht
          by_contra h
          simp [h, Savitch.firstBitD] at ht
    · intro h
      exact ⟨1, by rw [Savitch.firstBitD_run_succ]; simp [h, Savitch.firstBitD]⟩

end CS

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

/-
# Bounded reachability and the Savitch recursion

`PathN E s n a b` says that there is a path of length exactly `n` from `a` to `b` for the edge
relation `E`, all of whose vertices, except possibly the last one, are words of length at most
`s`.

`savR E s k a b` is the midpoint recursion of Savitch's algorithm; it decides whether `b` can be
reached from `a` by a path of length at most `2 ^ k` inside the set of words of length `≤ s`.
-/
import RequestProject.Savitch.Words

namespace CS
namespace Savitch

variable {E : Word → Word → Bool} {s : ℕ}

/-- A path of length `n` from `a` to `b`, staying (except possibly for its last vertex)
inside the words of length at most `s`. -/
def PathN (E : Word → Word → Bool) (s n : ℕ) (a b : Word) : Prop :=
  ∃ p : ℕ → Word, p 0 = a ∧ p n = b ∧ ∀ i < n, (p i).length ≤ s ∧ E (p i) (p (i + 1)) = true

theorem PathN.refl (E : Word → Word → Bool) (s : ℕ) (a : Word) : PathN E s 0 a a :=
  ⟨fun _ => a, rfl, rfl, by omega⟩

theorem PathN.of_eq {a b : Word} (h : a = b) : PathN E s 0 a b := h ▸ PathN.refl E s a

theorem PathN.zero_iff {a b : Word} : PathN E s 0 a b ↔ a = b := by
  constructor
  · rintro ⟨p, h0, h1, -⟩; rw [← h0, h1]
  · exact PathN.of_eq

theorem PathN.single {a b : Word} (ha : a.length ≤ s) (hE : E a b = true) :
    PathN E s 1 a b := by
  refine ⟨fun i => if i = 0 then a else b, by simp, by simp, ?_⟩
  intro i hi
  interval_cases i
  simpa using ⟨ha, hE⟩

theorem PathN.edge_of_one {a b : Word} (h : PathN E s 1 a b) : E a b = true := by
  obtain ⟨p, h0, h1, hp⟩ := h
  have := (hp 0 (by omega)).2
  rw [h0] at this
  simpa [h1] using this

/-- Composition of paths. -/
theorem PathN.comp {n₁ n₂ : ℕ} {a m b : Word} (h₁ : PathN E s n₁ a m) (h₂ : PathN E s n₂ m b)
    (hm : m.length ≤ s) : PathN E s (n₁ + n₂) a b := by
  obtain ⟨p, hp0, hp1, hp⟩ := h₁
  obtain ⟨q, hq0, hq1, hq⟩ := h₂
  refine ⟨fun t => if t ≤ n₁ then p t else q (t - n₁), ?_, ?_, ?_⟩
  · simpa using hp0
  · rcases Nat.eq_zero_or_pos n₂ with h | h
    · subst h
      have hmb : m = b := hq0.symm.trans hq1
      simp only [Nat.add_zero, le_refl, if_true]
      rw [hp1, hmb]
    · have : ¬ n₁ + n₂ ≤ n₁ := by omega
      simp only [this, if_false]
      simpa using hq1
  · intro i hi
    rcases lt_trichotomy i n₁ with h | h | h
    · have h1 : i ≤ n₁ := by omega
      have h2 : i + 1 ≤ n₁ := by omega
      simp only [h1, h2, if_true]
      exact hp i h
    · subst h
      have h2 : ¬ i + 1 ≤ i := by omega
      simp only [le_refl, if_true, h2, if_false]
      have := hq 0 (by omega)
      rw [hq0] at this
      refine ⟨by rw [hp1]; exact hm, ?_⟩
      have hii : i + 1 - i = 1 := by omega
      rw [hii, hp1]
      exact this.2
    · have h1 : ¬ i ≤ n₁ := by omega
      have h2 : ¬ i + 1 ≤ n₁ := by omega
      simp only [h1, h2, if_false]
      have hlt : i - n₁ < n₂ := by omega
      have := hq (i - n₁) hlt
      have hii : i + 1 - n₁ = (i - n₁) + 1 := by omega
      rw [hii]
      exact this

/-- Every prefix of a path is a path. -/
theorem PathN.prefix {n : ℕ} {a b : Word} (h : PathN E s n a b) (i : ℕ) (hi : i ≤ n) :
    ∃ m, PathN E s i a m ∧ PathN E s (n - i) m b ∧ (m.length ≤ s ∨ m = b) := by
  obtain ⟨p, hp0, hp1, hp⟩ := h
  refine ⟨p i, ⟨p, hp0, rfl, fun j hj => hp j (by omega)⟩,
    ⟨fun t => p (i + t), by simp, ?_, ?_⟩, ?_⟩
  · show p (i + (n - i)) = b
    rw [show i + (n - i) = n by omega]; exact hp1
  · intro j hj
    have := hp (i + j) (by omega)
    rw [show i + j + 1 = i + (j + 1) by omega] at this
    exact this
  · rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · exact Or.inr (by rw [← heq] at hp1; exact hp1)
    · exact Or.inl (hp i hlt).1

/-- A path visiting more than `wordCount s` vertices can be shortened. -/
theorem PathN.shorten_step {n : ℕ} {a b : Word} (h : PathN E s n a b) (hb : b.length ≤ s)
    (hn : wordCount s ≤ n) : ∃ n' < n, PathN E s n' a b := by
  obtain ⟨p, hp0, hp1, hp⟩ := h
  have hlen : ∀ i ≤ n, (p i).length ≤ s := by
    intro i hi
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · rw [heq, hp1]; exact hb
    · exact (hp i hlt).1
  have hmaps : ∀ i ∈ Finset.range (n + 1), wrank (p i) ∈ Finset.range (wordCount s) := by
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    exact wrank_lt_wordCount (hlen i (by omega))
  have hcard : (Finset.range (wordCount s)).card < (Finset.range (n + 1)).card := by
    simp only [Finset.card_range]; omega
  obtain ⟨i, hi, j, hj, hij, hval⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [Finset.mem_range] at hi hj
  have hpij : p i = p j := wrank_injective hval
  -- WLOG `i < j`
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i + (n - j), by omega, ?_⟩
    refine PathN.comp (m := p i) ⟨p, hp0, rfl, fun t ht => hp t (by omega)⟩ ?_ (hlen i (by omega))
    refine ⟨fun t => p (j + t), by simp [hpij], ?_, ?_⟩
    · show p (j + (n - j)) = b
      rw [show j + (n - j) = n by omega]; exact hp1
    intro t ht
    have := hp (j + t) (by omega)
    rw [show j + t + 1 = j + (t + 1) by omega] at this
    exact this
  · refine ⟨j + (n - i), by omega, ?_⟩
    refine PathN.comp (m := p j) ⟨p, hp0, rfl, fun t ht => hp t (by omega)⟩ ?_ (hlen j (by omega))
    refine ⟨fun t => p (i + t), by simp [hpij], ?_, ?_⟩
    · show p (i + (n - i)) = b
      rw [show i + (n - i) = n by omega]; exact hp1
    intro t ht
    have := hp (i + t) (by omega)
    rw [show i + t + 1 = i + (t + 1) by omega] at this
    exact this

/-- Any path can be shortened to one of length less than the number of available vertices. -/
theorem PathN.shorten {n : ℕ} {a b : Word} (h : PathN E s n a b) (hb : b.length ≤ s) :
    ∃ n' < wordCount s, PathN E s n' a b := by
  induction n using Nat.strong_induction_on generalizing a with
  | _ n ih =>
      by_cases hn : n < wordCount s
      · exact ⟨n, hn, h⟩
      · obtain ⟨n', hn', h'⟩ := h.shorten_step hb (by omega)
        exact ih n' hn' h'

/-- The Savitch midpoint recursion: `savR E s k a b` decides reachability from `a` to `b` by a
path of length at most `2 ^ k` inside the words of length at most `s`. -/
def savR (E : Word → Word → Bool) (s : ℕ) : ℕ → Word → Word → Bool
  | 0, a, b => (a == b) || E a b
  | k + 1, a, b =>
      (a == b) || anyMid (fun m => savR E s k a m && savR E s k m b) (wordCount s) []

theorem savR_zero (E : Word → Word → Bool) (s : ℕ) (a b : Word) :
    savR E s 0 a b = ((a == b) || E a b) := rfl

theorem savR_succ (E : Word → Word → Bool) (s k : ℕ) (a b : Word) :
    savR E s (k + 1) a b =
      ((a == b) || anyMid (fun m => savR E s k a m && savR E s k m b) (wordCount s) []) := rfl

/-- Correctness of the Savitch recursion. -/
theorem savR_iff (E : Word → Word → Bool) (s : ℕ) :
    ∀ (k : ℕ) {a b : Word}, a.length ≤ s → b.length ≤ s →
      (savR E s k a b = true ↔ ∃ n ≤ 2 ^ k, PathN E s n a b) := by
  intro k
  induction k with
  | zero =>
      intro a b ha _
      rw [savR_zero]
      constructor
      · intro h
        rw [Bool.or_eq_true] at h
        rcases h with h1 | h1
        · exact ⟨0, by norm_num, PathN.of_eq (by simpa using h1)⟩
        · exact ⟨1, by norm_num, PathN.single ha h1⟩
      · rintro ⟨n, hn, hp⟩
        have : n = 0 ∨ n = 1 := by simp at hn; omega
        rcases this with rfl | rfl
        · rw [PathN.zero_iff] at hp; simp [hp]
        · simp [hp.edge_of_one]
  | succ k ih =>
      intro a b ha hb
      rw [savR_succ]
      constructor
      · intro h
        rw [Bool.or_eq_true] at h
        rcases h with h1 | h1
        · exact ⟨0, by positivity, PathN.of_eq (by simpa using h1)⟩
        · obtain ⟨m, hm, hP⟩ := (anyMid_all _ s).1 h1
          rw [Bool.and_eq_true] at hP
          obtain ⟨n₁, hn₁, hp₁⟩ := (ih ha hm).1 hP.1
          obtain ⟨n₂, hn₂, hp₂⟩ := (ih hm hb).1 hP.2
          exact ⟨n₁ + n₂, by rw [pow_succ]; omega, hp₁.comp hp₂ hm⟩
      · rintro ⟨n, hn, hp⟩
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · rw [PathN.zero_iff] at hp; simp [hp]
        · have hle : min n (2 ^ k) ≤ n := min_le_left _ _
          obtain ⟨m, hpre, hsuf, hmem⟩ := hp.prefix (min n (2 ^ k)) hle
          have hmlen : m.length ≤ s := by
            rcases hmem with h | h
            · exact h
            · rw [h]; exact hb
          have h1 : min n (2 ^ k) ≤ 2 ^ k := min_le_right _ _
          have h2 : n - min n (2 ^ k) ≤ 2 ^ k := by
            rw [pow_succ] at hn
            rcases le_total n (2 ^ k) with h | h
            · simp [min_eq_left h]
            · simp [min_eq_right h]; omega
          have hA : savR E s k a m = true := (ih ha hmlen).2 ⟨_, h1, hpre⟩
          have hB : savR E s k m b = true := (ih hmlen hb).2 ⟨_, h2, hsuf⟩
          rw [Bool.or_eq_true]
          exact Or.inr ((anyMid_all _ s).2 ⟨m, hmlen, by simp [hA, hB]⟩)

/-- Reachability inside the words of length at most `s` is decided by `savR` at level `s + 1`. -/
theorem savR_reach_iff (E : Word → Word → Bool) (s : ℕ) {a b : Word}
    (ha : a.length ≤ s) (hb : b.length ≤ s) :
    savR E s (s + 1) a b = true ↔ ∃ n, PathN E s n a b := by
  constructor
  · intro h
    obtain ⟨n, -, hp⟩ := (savR_iff E s (s + 1) ha hb).1 h
    exact ⟨n, hp⟩
  · rintro ⟨n, hp⟩
    obtain ⟨n', hn', hp'⟩ := hp.shorten hb
    refine (savR_iff E s (s + 1) ha hb).2 ⟨n', ?_, hp'⟩
    have hw : wordCount s ≤ 2 ^ (s + 1) := by
      simp only [wordCount]
      exact Nat.sub_le _ _
    exact le_of_lt (lt_of_lt_of_le hn' hw)

end Savitch
end CS

/-
# Correctness of the simulator

The simulator implements the Savitch recursion `savR` with an explicit stack, and scans all
words of length at most the current stage, looking for a reachable accepting configuration and
for a reachable configuration that leaves the current stage.
-/
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Encode

namespace CS
namespace Savitch

variable {M : NMachine} {x : Word} {stage : ℕ} {target : Word} {acc esc : Bool}

/-- `Runs M x σ σ'` : the simulator started in state `σ` reaches state `σ'`. -/
def Runs (M : NMachine) (x : Word) (σ σ' : SState) : Prop :=
  ∃ t, dstepIter M x t σ = σ'

theorem Runs.refl (M : NMachine) (x : Word) (σ : SState) : Runs M x σ σ := ⟨0, rfl⟩

theorem Runs.trans {σ σ' σ'' : SState} (h₁ : Runs M x σ σ') (h₂ : Runs M x σ' σ'') :
    Runs M x σ σ'' := by
  obtain ⟨t₁, h₁⟩ := h₁
  obtain ⟨t₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by rw [dstepIter_add, h₁, h₂]⟩

theorem Runs.one {σ σ' : SState} (h : dstep M x σ = σ') : Runs M x σ σ' :=
  ⟨1, by rw [dstepIter_succ, dstepIter_zero, h]⟩

theorem Runs.step {σ σ' σ'' : SState} (h : dstep M x σ = σ') (h' : Runs M x σ' σ'') :
    Runs M x σ σ'' := (Runs.one h).trans h'

/-! ## One-step computations of the simulator -/

theorem dstep_call_zero (a b : Word) (stack : List Frame) :
    dstep M x ⟨stage, target, acc, esc, Inner.call 0 a b, stack, none⟩
      = ⟨stage, target, acc, esc, Inner.ret ((a == b) || edgeB M x a b), stack, none⟩ := rfl

theorem dstep_call_succ_eq {k : ℕ} {a b : Word} (stack : List Frame) (h : a = b) :
    dstep M x ⟨stage, target, acc, esc, Inner.call (k + 1) a b, stack, none⟩
      = ⟨stage, target, acc, esc, Inner.ret true, stack, none⟩ := by
  simp [dstep, sstep, sstepAux, h]

theorem dstep_call_succ_ne {k : ℕ} {a b : Word} (stack : List Frame) (h : a ≠ b) :
    dstep M x ⟨stage, target, acc, esc, Inner.call (k + 1) a b, stack, none⟩
      = ⟨stage, target, acc, esc, Inner.call k a [], ⟨k, a, b, [], false⟩ :: stack, none⟩ := by
  simp [dstep, sstep, sstepAux, h]

theorem dstep_ret_second_true {k : ℕ} {a b mid : Word} (rest : List Frame) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret true, ⟨k, a, b, mid, true⟩ :: rest, none⟩
      = ⟨stage, target, acc, esc, Inner.ret true, rest, none⟩ := rfl

theorem dstep_ret_first_true {k : ℕ} {a b mid : Word} (rest : List Frame) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret true, ⟨k, a, b, mid, false⟩ :: rest, none⟩
      = ⟨stage, target, acc, esc, Inner.call k mid b, ⟨k, a, b, mid, true⟩ :: rest, none⟩ := rfl

theorem dstep_ret_false_some {k : ℕ} {a b mid m' : Word} {sec : Bool} (rest : List Frame)
    (h : univNext stage mid = some m') :
    dstep M x ⟨stage, target, acc, esc, Inner.ret false, ⟨k, a, b, mid, sec⟩ :: rest, none⟩
      = ⟨stage, target, acc, esc, Inner.call k a m', ⟨k, a, b, m', false⟩ :: rest, none⟩ := by
  cases sec <;> simp [dstep, sstep, sstepAux, advanceMid, h]

theorem dstep_ret_false_none {k : ℕ} {a b mid : Word} {sec : Bool} (rest : List Frame)
    (h : univNext stage mid = none) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret false, ⟨k, a, b, mid, sec⟩ :: rest, none⟩
      = ⟨stage, target, acc, esc, Inner.ret false, rest, none⟩ := by
  cases sec <;> simp [dstep, sstep, sstepAux, advanceMid, h]

theorem dstep_scan_some {v : Bool} {t' : Word} (h : univNext stage target = some t') :
    dstep M x ⟨stage, target, acc, esc, Inner.ret v, [], none⟩
      = ⟨stage, t', acc || (v && (M.verdict target == some true)),
          esc || (v && escapes M x[M.ask target]? stage target),
          Inner.call (stage + 1) [] t', [], none⟩ := by
  simp only [dstep, askWord, sstep, sstepAux, h]
  simp

theorem dstep_scan_none_acc {v : Bool} (h : univNext stage target = none)
    (hacc : (acc || (v && (M.verdict target == some true))) = true) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret v, [], none⟩
      = ⟨stage, target, acc || (v && (M.verdict target == some true)),
          esc || (v && escapes M x[M.ask target]? stage target),
          Inner.ret v, [], some true⟩ := by
  simp only [dstep, askWord, sstep, sstepAux, h, if_true]
  rw [if_pos hacc]

theorem dstep_scan_none_esc {v : Bool} (h : univNext stage target = none)
    (hacc : (acc || (v && (M.verdict target == some true))) = false)
    (hesc : (esc || (v && escapes M x[M.ask target]? stage target)) = true) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret v, [], none⟩
      = ⟨stage + 1, [], false, false, Inner.call (stage + 2) [] [], [], none⟩ := by
  simp only [dstep, askWord, sstep, sstepAux, h, if_true]
  rw [if_neg (by simp [hacc]), if_pos hesc]

theorem dstep_scan_none_rej {v : Bool} (h : univNext stage target = none)
    (hacc : (acc || (v && (M.verdict target == some true))) = false)
    (hesc : (esc || (v && escapes M x[M.ask target]? stage target)) = false) :
    dstep M x ⟨stage, target, acc, esc, Inner.ret v, [], none⟩
      = ⟨stage, target, acc || (v && (M.verdict target == some true)),
          esc || (v && escapes M x[M.ask target]? stage target),
          Inner.ret v, [], some false⟩ := by
  simp only [dstep, askWord, sstep, sstepAux, h, if_true]
  rw [if_neg (by simp [hacc]), if_neg (by simp [hesc])]

/-! ## The recursion is computed correctly -/

/-- The simulator, started on a pending call, eventually returns the value of the Savitch
recursion, leaving the rest of the state unchanged. -/
theorem call_run (M : NMachine) (x : Word) (stage : ℕ) (target : Word) (acc esc : Bool) :
    ∀ (k : ℕ) (a b : Word) (stack : List Frame),
      Runs M x ⟨stage, target, acc, esc, Inner.call k a b, stack, none⟩
        ⟨stage, target, acc, esc, Inner.ret (savR (edgeB M x) stage k a b), stack, none⟩ := by
  intro k
  induction k with
  | zero =>
      intro a b stack
      exact Runs.one (by rw [dstep_call_zero, savR_zero])
  | succ k ih =>
      have loop : ∀ (n : ℕ) (a b mid : Word) (stack : List Frame),
          rem stage mid = n → mid.length ≤ stage →
          Runs M x
              ⟨stage, target, acc, esc, Inner.call k a mid, ⟨k, a, b, mid, false⟩ :: stack, none⟩
              ⟨stage, target, acc, esc,
                Inner.ret (anyMid (fun m => savR (edgeB M x) stage k a m &&
                                            savR (edgeB M x) stage k m b) n mid),
                stack, none⟩ := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihn =>
          intro a b mid stack hrem hmid
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
            have := rem_pos (s := stage) hmid
            exact ⟨n - 1, by omega⟩
          set E := edgeB M x with hE
          set P : Word → Bool := fun w => savR E stage k a w && savR E stage k w b with hP
          -- advancing to the next midpoint
          have adv : ∀ (sec : Bool), P mid = false →
              Runs M x
                ⟨stage, target, acc, esc, Inner.ret false, ⟨k, a, b, mid, sec⟩ :: stack, none⟩
                ⟨stage, target, acc, esc, Inner.ret (anyMid P (m + 1) mid), stack, none⟩ := by
            intro sec hPmid
            rw [anyMid_succ, hPmid, Bool.false_or]
            by_cases h2 : 2 ≤ rem stage mid
            · obtain ⟨hsome, hlen⟩ := univNext_eq_some hmid h2
              refine Runs.step (dstep_ret_false_some stack hsome) ?_
              exact ihn m (by omega) a b (wnext mid) stack (by rw [rem_wnext, hrem]; omega) hlen
            · have hnone : univNext stage mid = none := (univNext_eq_none hmid).2 (by omega)
              have hm : m = 0 := by omega
              subst hm
              refine Runs.one ?_
              rw [dstep_ret_false_none stack hnone]
              simp [anyMid]
          by_cases hv1 : savR E stage k a mid = true
          · refine (ih a mid (⟨k, a, b, mid, false⟩ :: stack)).trans ?_
            rw [hv1]
            refine Runs.step (dstep_ret_first_true stack) ?_
            refine (ih mid b (⟨k, a, b, mid, true⟩ :: stack)).trans ?_
            by_cases hv2 : savR E stage k mid b = true
            · rw [hv2]
              refine Runs.one ?_
              rw [dstep_ret_second_true stack]
              have hPmid : P mid = true := by simp [hP, hv1, hv2]
              rw [anyMid_succ, hPmid, Bool.true_or]
            · have hv2' : savR E stage k mid b = false := by simpa using hv2
              rw [hv2']
              exact adv true (by simp [hP, hv2'])
          · have hv1' : savR E stage k a mid = false := by simpa using hv1
            refine (ih a mid (⟨k, a, b, mid, false⟩ :: stack)).trans ?_
            rw [hv1']
            exact adv false (by simp [hP, hv1'])
      intro a b stack
      by_cases hab : a = b
      · refine Runs.one ?_
        rw [dstep_call_succ_eq stack hab]
        congr 1
        rw [savR_succ]
        simp [hab]
      · refine Runs.step (dstep_call_succ_ne stack hab) ?_
        have h2 := loop (rem stage ([] : Word)) a b [] stack rfl (by simp)
        refine h2.trans ?_
        have hrem : rem stage ([] : Word) = wordCount stage := by simp [rem]
        rw [hrem, savR_succ, show (a == b) = false from beq_eq_false_iff_ne.2 hab,
          Bool.false_or]
        exact Runs.refl M x _

/-! ## The scan over all candidate configurations -/

/-- Started at the target `c`, the simulator scans all remaining targets, and then either halts
or moves to the next stage, according to the two flags it has accumulated. -/
theorem scan_run (M : NMachine) (x : Word) (stage : ℕ) :
    ∀ (n : ℕ) (c : Word) (acc esc : Bool), rem stage c = n → c.length ≤ stage →
      ∃ σ', Runs M x ⟨stage, c, acc, esc, Inner.call (stage + 1) [] c, [], none⟩ σ' ∧
        (if (acc || anyMid (accP M x stage) n c) = true then
            σ'.done = some true ∧ σ'.stage = stage
          else if (esc || anyMid (escP M x stage) n c) = true then
            σ' = ⟨stage + 1, [], false, false, Inner.call (stage + 2) [] [], [], none⟩
          else σ'.done = some false ∧ σ'.stage = stage) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro c acc esc hrem hc
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := rem_pos (s := stage) hc; omega⟩
    have hstart := call_run M x stage c acc esc (stage + 1) [] c []
    by_cases h2 : 2 ≤ rem stage c
    · obtain ⟨hsome, hlen⟩ := univNext_eq_some hc h2
      obtain ⟨σ', hrun, hprop⟩ := ihn m (by omega) (wnext c)
        (acc || accP M x stage c) (esc || escP M x stage c)
        (by rw [rem_wnext, hrem]; omega) hlen
      refine ⟨σ', hstart.trans ((Runs.one (dstep_scan_some hsome)).trans hrun), ?_⟩
      rw [anyMid_succ, anyMid_succ, ← Bool.or_assoc, ← Bool.or_assoc]
      exact hprop
    · have hnone : univNext stage c = none := (univNext_eq_none hc).2 (by omega)
      have hm : m = 0 := by omega
      subst hm
      have hA1 : anyMid (accP M x stage) 1 c = accP M x stage c := by simp [anyMid]
      have hX1 : anyMid (escP M x stage) 1 c = escP M x stage c := by simp [anyMid]
      rw [hA1, hX1]
      by_cases hA : (acc || accP M x stage c) = true
      · refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_acc hnone hA)), ?_⟩
        rw [if_pos hA]
        exact ⟨rfl, rfl⟩
      · have hA' : (acc || accP M x stage c) = false := by simpa using hA
        by_cases hX : (esc || escP M x stage c) = true
        · refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_esc hnone hA' hX)), ?_⟩
          rw [if_neg hA, if_pos hX]
        · have hX' : (esc || escP M x stage c) = false := by simpa using hX
          refine ⟨_, hstart.trans (Runs.one (dstep_scan_none_rej hnone hA' hX')), ?_⟩
          rw [if_neg hA, if_neg hX]
          exact ⟨rfl, rfl⟩

/-! ## The simulator halts with the right answer -/

theorem sim_halts_aux (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) :
    ∀ (d stage : ℕ), S - stage = d → stage ≤ S →
      ∃ σ', Runs M x ⟨stage, [], false, false, Inner.call (stage + 1) [] [], [], none⟩ σ' ∧
        σ'.stage ≤ S ∧ σ'.done ≠ none ∧ (σ'.done = some true ↔ x ∈ M.lang) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro stage hd hstage
    obtain ⟨σ', hrun, hprop⟩ :=
      scan_run M x stage (rem stage ([] : Word)) [] false false rfl (by simp)
    have hrem : rem stage ([] : Word) = wordCount stage := by simp [rem]
    rw [hrem] at hprop
    by_cases hA : (false || anyMid (accP M x stage) (wordCount stage) []) = true
    · rw [if_pos hA] at hprop
      obtain ⟨hdone, hst⟩ := hprop
      have hlang : x ∈ M.lang := by
        rw [Bool.false_or, anyMid_all] at hA
        obtain ⟨u, hu, hacc⟩ := hA
        exact accP_sound hu hacc
      exact ⟨σ', hrun, by omega, by rw [hdone]; simp, by rw [hdone]; simp [hlang]⟩
    · rw [if_neg hA] at hprop
      have hA' : ∀ u : Word, u.length ≤ stage → accP M x stage u = false := by
        intro u hu
        by_contra hcon
        exact hA (by rw [Bool.false_or, anyMid_all]; exact ⟨u, hu, by simpa using hcon⟩)
      by_cases hX : (false || anyMid (escP M x stage) (wordCount stage) []) = true
      · rw [if_pos hX] at hprop
        -- the stage must be increased; this cannot happen at stage `S`
        have hlt : stage < S := by
          rcases Nat.lt_or_ge stage S with h | h
          · exact h
          · exfalso
            have hstageS : stage = S := by omega
            subst hstageS
            rw [Bool.false_or, anyMid_all] at hX
            obtain ⟨u, hu, hesc⟩ := hX
            rw [escP_eq_false_of_bound hS u hu] at hesc
            exact Bool.false_ne_true hesc
        obtain ⟨σ'', hrun'', hrest⟩ := ihd (S - (stage + 1)) (by omega) (stage + 1) rfl (by omega)
        exact ⟨σ'', hrun.trans (hprop ▸ hrun''), hrest⟩
      · rw [if_neg hX] at hprop
        obtain ⟨hdone, hst⟩ := hprop
        have hX' : ∀ u : Word, u.length ≤ stage → escP M x stage u = false := by
          intro u hu
          by_contra hcon
          exact hX (by rw [Bool.false_or, anyMid_all]; exact ⟨u, hu, by simpa using hcon⟩)
        have hnot : x ∉ M.lang := by
          rintro ⟨c, hreach, hver⟩
          obtain ⟨hlen, hsav⟩ := savR_complete_of_no_escape hX' c hreach
          have : accP M x stage c = true := by simp [accP, hsav, hver]
          rw [hA' c hlen] at this
          exact Bool.false_ne_true this
        refine ⟨σ', hrun, by omega, by rw [hdone]; simp, ?_⟩
        rw [hdone]
        simp [hnot]

theorem sim_halts (M : NMachine) (x : Word) (S : ℕ) (hS : ∀ c, M.Reach x c → c.length ≤ S) :
    ∃ σ', Runs M x initState σ' ∧ σ'.stage ≤ S ∧ σ'.done ≠ none ∧
      (σ'.done = some true ↔ x ∈ M.lang) :=
  sim_halts_aux M x S hS S 0 (by omega) (by omega)

end Savitch
end CS

/-
# Enumerating the words of length at most `s`

Savitch's algorithm has to loop over all configurations, i.e. over all words of length at most
`s`, while storing only the current word.  We therefore fix an explicit enumeration of *all*
words, given by the successor function `wnext`, whose position function is `wrank`.
-/
import RequestProject.Savitch.Model

namespace CS
namespace Savitch

/-- The successor of a word in the enumeration of all words
(binary counting, least significant bit first). -/
def wnext : Word → Word
  | [] => [false]
  | false :: t => true :: t
  | true :: t => false :: wnext t

/-- The position of a word in the enumeration given by `wnext`. -/
def wrank : Word → ℕ
  | [] => 0
  | b :: t => b.toNat + 2 * wrank t + 1

@[simp] theorem wrank_nil : wrank [] = 0 := rfl

theorem wrank_cons (b : Bool) (t : Word) :
    wrank (b :: t) = b.toNat + 2 * wrank t + 1 := rfl

theorem wrank_wnext (w : Word) : wrank (wnext w) = wrank w + 1 := by
  induction w with
  | nil => rfl
  | cons b t ih =>
      cases b <;>
        simp only [wnext, wrank_cons, ih, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem wrank_pos_of_cons (b : Bool) (t : Word) : 0 < wrank (b :: t) := by
  simp only [wrank_cons]; omega

theorem wrank_injective : Function.Injective wrank := by
  intro w
  induction w with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons b t => exact absurd hv.symm (Nat.ne_of_gt (wrank_pos_of_cons b t))
  | cons b t ih =>
      intro v hv
      cases v with
      | nil => exact absurd hv (Nat.ne_of_gt (wrank_pos_of_cons b t))
      | cons b' t' =>
          have h : b.toNat + 2 * wrank t + 1 = b'.toNat + 2 * wrank t' + 1 := hv
          have hbb : b = b' := by
            cases b <;> cases b' <;>
              simp only [Bool.toNat_true, Bool.toNat_false] at h <;>
              first | rfl | (exfalso; omega)
          subst hbb
          have ht : wrank t = wrank t' := by
            cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at h <;> omega
          rw [ih ht]

/-- Upper bound for the rank of a word of length `n`: `wrank w < 2 ^ (n + 1) - 1`. -/
theorem wrank_add_two_le (w : Word) : wrank w + 2 ≤ 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp
  | cons b t ih =>
      have : (2 : ℕ) ^ (t.length + 1 + 1) = 2 * 2 ^ (t.length + 1) := by ring
      simp only [List.length_cons, wrank_cons, this]
      cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Lower bound for the rank of a word of length `n`: `2 ^ n ≤ wrank w + 1`. -/
theorem pow_le_wrank_add_one (w : Word) : 2 ^ w.length ≤ wrank w + 1 := by
  induction w with
  | nil => simp
  | cons b t ih =>
      have : (2 : ℕ) ^ (t.length + 1) = 2 * 2 ^ t.length := by ring
      simp only [List.length_cons, wrank_cons, this]
      cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The number of words of length at most `s`. -/
def wordCount (s : ℕ) : ℕ := 2 ^ (s + 1) - 1

theorem length_le_iff_wrank_lt (w : Word) (s : ℕ) :
    w.length ≤ s ↔ wrank w < wordCount s := by
  have h1 := wrank_add_two_le w
  have h2 := pow_le_wrank_add_one w
  have hpos : 0 < 2 ^ (s + 1) := Nat.two_pow_pos _
  constructor
  · intro h
    have : (2 : ℕ) ^ (w.length + 1) ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [wordCount]
    omega
  · intro h
    simp only [wordCount] at h
    by_contra hc
    push_neg at hc
    have : (2 : ℕ) ^ (s + 1) ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem wrank_lt_wordCount {w : Word} {s : ℕ} (h : w.length ≤ s) : wrank w < wordCount s :=
  (length_le_iff_wrank_lt w s).1 h

/-- The next word of length at most `s`, if there is one. -/
def univNext (s : ℕ) (w : Word) : Option Word :=
  if (wnext w).length ≤ s then some (wnext w) else none

/-- The number of words of length at most `s` with rank at least the rank of `w`. -/
def rem (s : ℕ) (w : Word) : ℕ := wordCount s - wrank w

theorem rem_pos {s : ℕ} {w : Word} (h : w.length ≤ s) : 0 < rem s w := by
  have := wrank_lt_wordCount h
  simp only [rem]; omega

theorem rem_wnext (s : ℕ) (w : Word) : rem s (wnext w) = rem s w - 1 := by
  simp [rem, wrank_wnext]
  omega

theorem univNext_eq_none {s : ℕ} {w : Word} (h : w.length ≤ s) :
    univNext s w = none ↔ rem s w = 1 := by
  have h1 := wrank_lt_wordCount h
  simp only [univNext, rem]
  constructor
  · intro hn
    by_contra hc
    have hlen : ¬ (wnext w).length ≤ s := by
      by_contra hle
      simp [hle] at hn
    have : ¬ (wrank (wnext w) < wordCount s) := by
      intro hlt
      exact hlen ((length_le_iff_wrank_lt _ _).2 hlt)
    rw [wrank_wnext] at this
    omega
  · intro hr
    have : ¬ (wrank (wnext w) < wordCount s) := by
      rw [wrank_wnext]; omega
    have hlen : ¬ (wnext w).length ≤ s := fun hle => this (wrank_lt_wordCount hle)
    simp [hlen]

theorem univNext_eq_some {s : ℕ} {w : Word} (h : w.length ≤ s) (h2 : 2 ≤ rem s w) :
    univNext s w = some (wnext w) ∧ (wnext w).length ≤ s := by
  have h1 := wrank_lt_wordCount h
  simp only [rem] at h2
  have : wrank (wnext w) < wordCount s := by rw [wrank_wnext]; omega
  have hlen : (wnext w).length ≤ s := (length_le_iff_wrank_lt _ _).2 this
  simp [univNext, hlen]

/-- `anyMid s P n m` tests the predicate `P` on the `n` words starting at `m` in the
enumeration.  This is exactly the loop over midpoints performed by Savitch's algorithm. -/
def anyMid (P : Word → Bool) : ℕ → Word → Bool
  | 0, _ => false
  | n + 1, m => P m || anyMid P n (wnext m)

theorem anyMid_succ (P : Word → Bool) (n : ℕ) (m : Word) :
    anyMid P (n + 1) m = (P m || anyMid P n (wnext m)) := rfl

theorem anyMid_eq_true_iff (P : Word → Bool) :
    ∀ (n : ℕ) (m : Word),
      anyMid P n m = true ↔ ∃ u, wrank m ≤ wrank u ∧ wrank u < wrank m + n ∧ P u = true := by
  intro n
  induction n with
  | zero => intro m; simp [anyMid]; omega
  | succ n ih =>
      intro m
      rw [anyMid_succ, Bool.or_eq_true, ih (wnext m), wrank_wnext]
      constructor
      · rintro (hP | ⟨u, h1, h2, h3⟩)
        · exact ⟨m, le_refl _, by omega, hP⟩
        · exact ⟨u, by omega, by omega, h3⟩
      · rintro ⟨u, h1, h2, h3⟩
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · left
          rw [wrank_injective heq]
          exact h3
        · exact Or.inr ⟨u, by omega, by omega, h3⟩

/-- The complete loop over all words of length at most `s`. -/
theorem anyMid_all (P : Word → Bool) (s : ℕ) :
    anyMid P (wordCount s) [] = true ↔ ∃ u, u.length ≤ s ∧ P u = true := by
  rw [anyMid_eq_true_iff]
  constructor
  · rintro ⟨u, -, h2, h3⟩
    refine ⟨u, ?_, h3⟩
    exact (length_le_iff_wrank_lt u s).2 (by simpa using h2)
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, by simp, by simpa using wrank_lt_wordCount h1, h2⟩

end Savitch
end CS

/-
# The deterministic machine produced by Savitch's construction

Putting everything together: the simulator is packaged as a `DMachine`, it accepts exactly the
language of `M`, and it runs in space `O (S ^ 2)` whenever `M` runs in space `S`.
-/
import RequestProject.Savitch.Correct

namespace CS
namespace Savitch

theorem dstepIter_succ' (M : NMachine) (x : Word) (t : ℕ) (σ : SState) :
    dstepIter M x (t + 1) σ = dstep M x (dstepIter M x t σ) :=
  Function.iterate_succ_apply' _ _ _

theorem run_succ (D : DMachine) (x : Word) (t : ℕ) :
    D.run x (t + 1) =
      if D.verdict (D.run x t) = none then D.next (D.run x t) x[D.ask (D.run x t)]?
      else D.run x t := rfl

/-- The deterministic machine simulating the nondeterministic machine `M`. -/
noncomputable def savitchD (M : NMachine) : DMachine where
  ask := fun m => M.ask (askWord (dec m))
  next := fun m bit => enc (sstep M bit (dec m))
  verdict := fun m => (dec m).done

theorem savitchD_run (M : NMachine) (x : Word) :
    ∀ t, (savitchD M).run x t = if t = 0 then [] else enc (dstepIter M x t initState) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev : dec ((savitchD M).run x t) = dstepIter M x t initState := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · simpa using dec_nil
        · rw [ih, if_neg (by omega), dec_enc]
      have hverd : (savitchD M).verdict ((savitchD M).run x t)
          = (dstepIter M x t initState).done := by
        show (dec ((savitchD M).run x t)).done = _
        rw [hprev]
      rw [if_neg (Nat.succ_ne_zero t), run_succ]
      by_cases hd : (dstepIter M x t initState).done = none
      · rw [if_pos (by rw [hverd]; exact hd)]
        show enc (sstep M x[M.ask (askWord (dec ((savitchD M).run x t)))]?
          (dec ((savitchD M).run x t))) = _
        rw [hprev, dstepIter_succ']
        rfl
      · rw [if_neg (by rw [hverd]; exact hd)]
        rw [dstepIter_succ', dstep_done hd]
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exact absurd (by simp [initState] : (dstepIter M x 0 initState).done = none) hd
        · rw [ih, if_neg (by omega)]

theorem savitchD_verdict_run (M : NMachine) (x : Word) (t : ℕ) :
    (savitchD M).verdict ((savitchD M).run x t) = (dstepIter M x t initState).done := by
  show (dec ((savitchD M).run x t)).done = _
  rw [savitchD_run]
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp [dec_nil]
  · rw [if_neg (by omega), dec_enc]

/-- Once the simulator has halted, its state no longer changes. -/
theorem frozen {M : NMachine} {x : Word} {σ : SState} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂)
    (hd : (dstepIter M x t₁ σ).done ≠ none) :
    dstepIter M x t₂ σ = dstepIter M x t₁ σ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [dstepIter_add]
  exact dstepIter_done hd d

theorem savitchD_lang (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) :
    (x ∈ (savitchD M).lang ↔ x ∈ M.lang) := by
  obtain ⟨σ', ⟨T, hT⟩, hstage, hdone, hiff⟩ := sim_halts M x S hS
  constructor
  · rintro ⟨t, ht⟩
    rw [savitchD_verdict_run] at ht
    have hne : (dstepIter M x t initState).done ≠ none := by rw [ht]; simp
    have hdone' : (dstepIter M x T initState).done ≠ none := by rw [hT]; exact hdone
    have hTdone : (dstepIter M x T initState).done = some true := by
      rcases le_total t T with hle | hle
      · rw [frozen hle hne, ht]
      · rw [← frozen hle hdone']
        exact ht
    rw [hT] at hTdone
    exact hiff.1 hTdone
  · intro hx
    refine ⟨T, ?_⟩
    rw [savitchD_verdict_run, hT]
    exact hiff.2 hx

theorem savitchD_stage_le (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) (t : ℕ) :
    (dstepIter M x t initState).stage ≤ S := by
  obtain ⟨σ', ⟨T, hT⟩, hstage, hdone, hiff⟩ := sim_halts M x S hS
  rcases le_total t T with hle | hle
  · have := stage_mono (M := M) (x := x) (σ := initState) hle
    rw [hT] at this
    omega
  · rw [frozen hle (by rw [hT]; exact hdone), hT]
    exact hstage

theorem savitchD_space (M : NMachine) (x : Word) (S : ℕ)
    (hS : ∀ c, M.Reach x c → c.length ≤ S) (t : ℕ) :
    ((savitchD M).run x t).length ≤ 25 * (S + 1) ^ 2 := by
  rw [savitchD_run]
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp
  · rw [if_neg (by omega)]
    have hInv : Inv (dstepIter M x t initState) :=
      Inv_dstepIter M x t initState Inv_initState
    have h1 := enc_length_le hInv
    have h2 : (dstepIter M x t initState).stage + 1 ≤ S + 1 := by
      have := savitchD_stage_le M x S hS t
      omega
    have h3 : ((dstepIter M x t initState).stage + 1) ^ 2 ≤ (S + 1) ^ 2 :=
      Nat.pow_le_pow_left h2 2
    omega

end Savitch
end CS

/-
# The deterministic simulator: states and transition

The deterministic machine simulating a nondeterministic space bounded machine `M` keeps in its
memory:

* the current *stage* `s` (the guess for the space bound of `M`);
* the current *target* configuration `c` (the configuration whose reachability is being tested);
* two flags recording whether an accepting configuration has been found reachable, and whether
  some reachable configuration can leave the set of words of length `≤ s`;
* the state of the recursive midpoint procedure: a *stack* of frames plus either a pending call
  or a pending return value.
-/
import RequestProject.Savitch.Paths

namespace CS
namespace Savitch

/-- One frame of the recursion stack: the pending computation
`∃ mid, savR k a mid ∧ savR k mid b`, where `second` says which of the two halves is
currently being evaluated. -/
structure Frame where
  k : ℕ
  a : Word
  b : Word
  mid : Word
  second : Bool
deriving DecidableEq, Inhabited

/-- The "program counter" of the recursion: either a pending call, or a value being returned. -/
inductive Inner where
  | call (k : ℕ) (a b : Word)
  | ret (v : Bool)
deriving DecidableEq, Inhabited

/-- The state of the deterministic simulator. -/
structure SState where
  stage : ℕ
  target : Word
  acc : Bool
  esc : Bool
  inner : Inner
  stack : List Frame
  done : Option Bool
deriving DecidableEq, Inhabited

/-- The initial state: stage `0`, first target the empty word. -/
def initState : SState := ⟨0, [], false, false, Inner.call 1 [] [], [], none⟩

/-- One step of `M` from `a` to `b`, computed from the single input bit that was read. -/
def leafEdge (M : NMachine) (bit : Option Bool) (a b : Word) : Bool :=
  (M.verdict a == none) && decide (b ∈ M.next a bit)

/-- Does `M` have a successor of `c` of length more than `s`? -/
def escapes (M : NMachine) (bit : Option Bool) (s : ℕ) (c : Word) : Bool :=
  (M.verdict c == none) && (M.next c bit).any (fun c' => decide (s < c'.length))

/-- Move to the next midpoint, or return `false` if the midpoints are exhausted. -/
def advanceMid (σ : SState) (fr : Frame) (rest : List Frame) : SState :=
  match univNext σ.stage fr.mid with
  | some m' =>
      { σ with inner := Inner.call fr.k fr.a m',
               stack := { fr with mid := m', second := false } :: rest }
  | none => { σ with inner := Inner.ret false, stack := rest }

/-- The transition of the simulator on a state that has not halted yet. -/
def sstepAux (M : NMachine) (bit : Option Bool) (σ : SState) : SState :=
  match σ.inner with
  | Inner.call 0 a b => { σ with inner := Inner.ret ((a == b) || leafEdge M bit a b) }
  | Inner.call (k + 1) a b =>
      if a = b then { σ with inner := Inner.ret true }
      else { σ with inner := Inner.call k a [],
                    stack := ⟨k, a, b, [], false⟩ :: σ.stack }
  | Inner.ret v =>
      match σ.stack with
      | [] =>
          let acc' := σ.acc || (v && (M.verdict σ.target == some true))
          let esc' := σ.esc || (v && escapes M bit σ.stage σ.target)
          match univNext σ.stage σ.target with
          | some t' =>
              { σ with target := t', acc := acc', esc := esc',
                       inner := Inner.call (σ.stage + 1) [] t' }
          | none =>
              if acc' then { σ with acc := acc', esc := esc', done := some true }
              else if esc' then
                ⟨σ.stage + 1, [], false, false, Inner.call (σ.stage + 2) [] [], [], none⟩
              else { σ with acc := acc', esc := esc', done := some false }
      | fr :: rest =>
          if fr.second then
            (if v then { σ with inner := Inner.ret true, stack := rest }
             else advanceMid σ fr rest)
          else
            (if v then { σ with inner := Inner.call fr.k fr.mid fr.b,
                                stack := { fr with second := true } :: rest }
             else advanceMid σ fr rest)

/-- The transition of the simulator. -/
def sstep (M : NMachine) (bit : Option Bool) (σ : SState) : SState :=
  if σ.done = none then sstepAux M bit σ else σ

/-- The configuration of `M` about which the simulator needs to read an input bit. -/
def askWord (σ : SState) : Word :=
  match σ.inner with
  | Inner.call 0 a _ => a
  | Inner.ret _ => match σ.stack with
      | [] => σ.target
      | _ => []
  | _ => []

/-- One step of the simulator on the input `x`. -/
def dstep (M : NMachine) (x : Word) (σ : SState) : SState :=
  sstep M x[M.ask (askWord σ)]? σ

/-- `t` steps of the simulator on the input `x`. -/
def dstepIter (M : NMachine) (x : Word) (t : ℕ) (σ : SState) : SState :=
  (dstep M x)^[t] σ

@[simp] theorem dstepIter_zero (M : NMachine) (x : Word) (σ : SState) :
    dstepIter M x 0 σ = σ := rfl

theorem dstepIter_succ (M : NMachine) (x : Word) (t : ℕ) (σ : SState) :
    dstepIter M x (t + 1) σ = dstepIter M x t (dstep M x σ) :=
  Function.iterate_succ_apply _ _ _

theorem dstepIter_add (M : NMachine) (x : Word) (t₁ t₂ : ℕ) (σ : SState) :
    dstepIter M x (t₁ + t₂) σ = dstepIter M x t₂ (dstepIter M x t₁ σ) := by
  simp only [dstepIter]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem dstep_done {M : NMachine} {x : Word} {σ : SState} (h : σ.done ≠ none) :
    dstep M x σ = σ := by
  rw [dstep, sstep, if_neg h]

theorem dstepIter_done {M : NMachine} {x : Word} {σ : SState} (h : σ.done ≠ none) (t : ℕ) :
    dstepIter M x t σ = σ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [dstepIter_succ, dstep_done h, ih]

/-- The stage of the simulator never decreases. -/
theorem stage_dstep_ge (M : NMachine) (x : Word) (σ : SState) :
    σ.stage ≤ (dstep M x σ).stage := by
  rcases σ with ⟨stage, target, acc, esc, inner, stack, done⟩
  by_cases hd : done = none
  · subst hd
    simp only [dstep, sstep, sstepAux, advanceMid]
    repeat' split
    all_goals simp
  · rw [dstep_done hd]

theorem stage_dstepIter_ge (M : NMachine) (x : Word) (σ : SState) (t : ℕ) :
    σ.stage ≤ (dstepIter M x t σ).stage := by
  induction t generalizing σ with
  | zero => exact le_refl _
  | succ t ih =>
      rw [dstepIter_succ]
      exact le_trans (stage_dstep_ge M x σ) (ih _)

theorem stage_mono {M : NMachine} {x : Word} {σ : SState} {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (dstepIter M x t₁ σ).stage ≤ (dstepIter M x t₂ σ).stage := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [dstepIter_add]
  exact stage_dstepIter_ge _ _ _ _

end Savitch
end CS

/-
# A machine model for space-bounded computation

We use the standard *off-line random-access* model of a space bounded machine:

* the input `x : List Bool` is read-only and is accessed one bit at a time, at a position
  which is determined by the current memory content (`ask`);
* the machine's whole workspace is a bit string `m : List Bool` (its *memory*); one step
  rewrites the memory using the current memory and the single input bit that was read;
* the *space* used on an input is the maximal length of a memory string occurring in a
  computation.

Nondeterministic machines have a list of possible successor memories, deterministic machines
exactly one.  A machine halts as soon as `verdict` of the current memory is `some b`.

Note that no computability assumption is placed on the three components `ask`, `next`,
`verdict` of a machine; they are arbitrary (possibly non-computable) functions of the memory.
This is the usual abstraction of "an arbitrary finite control", and it is what makes the
*space* bound the only resource restriction.  It is a genuine restriction: a machine whose
memory is bounded by `g (|x|)` bits can only ever be in one of `2 ^ (g |x| + 1) - 1` memory
states, and it can only see the input through the single bit it reads at each step.
-/
import Mathlib

namespace CS

/-- Words (bit strings): inputs, and memory contents, are words. -/
abbrev Word := List Bool

/-- A language is a set of words. -/
abbrev Language := Set Word

/-- A nondeterministic space-bounded machine. -/
structure NMachine where
  /-- Position of the input bit that is read, as a function of the current memory. -/
  ask : Word → ℕ
  /-- Possible successor memories, given the current memory and the input bit that was read
  (`none` if the position is beyond the end of the input). -/
  next : Word → Option Bool → List Word
  /-- `none` means "keep computing", `some b` means "halt and output `b`". -/
  verdict : Word → Option Bool

/-- A deterministic space-bounded machine. -/
structure DMachine where
  /-- Position of the input bit that is read, as a function of the current memory. -/
  ask : Word → ℕ
  /-- The successor memory, given the current memory and the input bit that was read. -/
  next : Word → Option Bool → Word
  /-- `none` means "keep computing", `some b` means "halt and output `b`". -/
  verdict : Word → Option Bool

namespace NMachine

variable (M : NMachine)

/-- One computation step of `M` on input `x`. -/
def StepRel (x : Word) (c c' : Word) : Prop :=
  M.verdict c = none ∧ c' ∈ M.next c x[M.ask c]?

/-- The memories reachable by `M` on input `x`, starting from the empty memory. -/
def Reach (x c : Word) : Prop :=
  Relation.ReflTransGen (M.StepRel x) [] c

/-- The language accepted by a nondeterministic machine: some computation branch accepts. -/
def lang : Language :=
  {x | ∃ c, M.Reach x c ∧ M.verdict c = some true}

/-- `M` uses at most `s` bits of memory on input `x`. -/
def SpaceBoundedOn (x : Word) (s : ℕ) : Prop :=
  ∀ c, M.Reach x c → c.length ≤ s

theorem reach_refl (x : Word) : M.Reach x [] := Relation.ReflTransGen.refl

theorem reach_step {x c c' : Word} (h : M.Reach x c) (h' : M.StepRel x c c') :
    M.Reach x c' := h.tail h'

end NMachine

namespace DMachine

variable (D : DMachine)

/-- The memory content of the deterministic machine `D` on input `x` after `t` steps. -/
def run (x : Word) : ℕ → Word
  | 0 => []
  | t + 1 =>
      let c := run x t
      if D.verdict c = none then D.next c x[D.ask c]? else c

/-- The language accepted by a deterministic machine. -/
def lang : Language :=
  {x | ∃ t, D.verdict (D.run x t) = some true}

/-- `D` uses at most `s` bits of memory on input `x`. -/
def SpaceBoundedOn (x : Word) (s : ℕ) : Prop :=
  ∀ t, (D.run x t).length ≤ s

end DMachine

/-- `NSPACE f`: languages accepted by a nondeterministic machine running in space `O (f n)`. -/
def NSPACE (f : ℕ → ℕ) : Set Language :=
  {L | ∃ (M : NMachine) (c : ℕ), (∀ x, M.SpaceBoundedOn x (c * f x.length + c)) ∧ M.lang = L}

/-- `DSPACE g`: languages accepted by a deterministic machine running in space `O (g n)`. -/
def DSPACE (g : ℕ → ℕ) : Set Language :=
  {L | ∃ (D : DMachine) (c : ℕ), (∀ x, D.SpaceBoundedOn x (c * g x.length + c)) ∧ D.lang = L}

/-- Polynomial space. -/
def PSPACE : Set Language := {L | ∃ k, L ∈ DSPACE (fun n => n ^ k)}

/-- Nondeterministic polynomial space. -/
def NPSPACE : Set Language := {L | ∃ k, L ∈ NSPACE (fun n => n ^ k)}

end CS

/-
# Encoding simulator states as bit strings

The memory of the deterministic machine is a bit string, so we encode the state of the
simulator with a simple self-delimiting code, and bound the length of the encoding by
`O (stage ^ 2)`.
-/
import RequestProject.Savitch.Sim

namespace CS
namespace Savitch

/-- Unary code of a natural number. -/
def codeN : ℕ → Word
  | 0 => [false]
  | n + 1 => true :: codeN n

/-- Self-delimiting code of a word. -/
def codeW : Word → Word
  | [] => [false]
  | b :: t => true :: b :: codeW t

/-- Code of a stack frame. -/
def codeFrame (f : Frame) : Word :=
  codeN f.k ++ codeW f.a ++ codeW f.b ++ codeW f.mid ++ [f.second]

/-- Code of a stack. -/
def codeStack : List Frame → Word
  | [] => [false]
  | f :: t => true :: (codeFrame f ++ codeStack t)

/-- Code of the recursion's program counter. -/
def codeInner : Inner → Word
  | Inner.call k a b => true :: (codeN k ++ codeW a ++ codeW b)
  | Inner.ret v => [false, v]

/-- Code of the halting status. -/
def codeDone : Option Bool → Word
  | none => [false]
  | some v => [true, v]

/-- Code of a simulator state. -/
def enc (σ : SState) : Word :=
  codeN σ.stage ++ codeW σ.target ++ [σ.acc, σ.esc] ++ codeDone σ.done ++
    codeInner σ.inner ++ codeStack σ.stack

/-! ## Injectivity -/

theorem codeN_app_inj : ∀ (m n : ℕ) (r₁ r₂ : Word),
    codeN m ++ r₁ = codeN n ++ r₂ → m = n ∧ r₁ = r₂ := by
  intro m
  induction m with
  | zero =>
      intro n r₁ r₂ h
      cases n with
      | zero => exact ⟨rfl, by simpa [codeN] using h⟩
      | succ n => simp [codeN] at h
  | succ m ih =>
      intro n r₁ r₂ h
      cases n with
      | zero => simp [codeN] at h
      | succ n =>
          simp only [codeN, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨h1, h2⟩ := ih n r₁ r₂ h
          exact ⟨by omega, h2⟩

theorem codeW_app_inj : ∀ (v w : Word) (r₁ r₂ : Word),
    codeW v ++ r₁ = codeW w ++ r₂ → v = w ∧ r₁ = r₂ := by
  intro v
  induction v with
  | nil =>
      intro w r₁ r₂ h
      cases w with
      | nil => exact ⟨rfl, by simpa [codeW] using h⟩
      | cons b t => simp [codeW] at h
  | cons b t ih =>
      intro w r₁ r₂ h
      cases w with
      | nil => simp [codeW] at h
      | cons b' t' =>
          simp only [codeW, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hb, h'⟩ := h
          obtain ⟨h1, h2⟩ := ih t' r₁ r₂ h'
          exact ⟨by rw [hb, h1], h2⟩

theorem codeFrame_app_inj (f g : Frame) (r₁ r₂ : Word)
    (h : codeFrame f ++ r₁ = codeFrame g ++ r₂) : f = g ∧ r₁ = r₂ := by
  simp only [codeFrame, List.append_assoc] at h
  obtain ⟨hk, h⟩ := codeN_app_inj _ _ _ _ h
  obtain ⟨ha, h⟩ := codeW_app_inj _ _ _ _ h
  obtain ⟨hb, h⟩ := codeW_app_inj _ _ _ _ h
  obtain ⟨hm, h⟩ := codeW_app_inj _ _ _ _ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨hs, hr⟩ := h
  refine ⟨?_, hr⟩
  cases f; cases g; simp_all

theorem codeStack_app_inj : ∀ (l₁ l₂ : List Frame) (r₁ r₂ : Word),
    codeStack l₁ ++ r₁ = codeStack l₂ ++ r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ r₁ r₂ h
      cases l₂ with
      | nil => exact ⟨rfl, by simpa [codeStack] using h⟩
      | cons f t => simp [codeStack] at h
  | cons f t ih =>
      intro l₂ r₁ r₂ h
      cases l₂ with
      | nil => simp [codeStack] at h
      | cons g t' =>
          simp only [codeStack, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hf, h⟩ := codeFrame_app_inj _ _ _ _ h
          obtain ⟨ht, hr⟩ := ih t' r₁ r₂ h
          exact ⟨by rw [hf, ht], hr⟩

theorem codeInner_app_inj (i j : Inner) (r₁ r₂ : Word)
    (h : codeInner i ++ r₁ = codeInner j ++ r₂) : i = j ∧ r₁ = r₂ := by
  cases i with
  | call k a b =>
      cases j with
      | call k' a' b' =>
          simp only [codeInner, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hk, h⟩ := codeN_app_inj _ _ _ _ h
          obtain ⟨ha, h⟩ := codeW_app_inj _ _ _ _ h
          obtain ⟨hb, hr⟩ := codeW_app_inj _ _ _ _ h
          exact ⟨by rw [hk, ha, hb], hr⟩
      | ret v => simp [codeInner] at h
  | ret v =>
      cases j with
      | call k' a' b' => simp [codeInner] at h
      | ret v' =>
          simp only [codeInner, List.cons_append, List.nil_append, List.cons.injEq,
            true_and] at h
          exact ⟨by rw [h.1], h.2⟩

theorem codeDone_app_inj (d e : Option Bool) (r₁ r₂ : Word)
    (h : codeDone d ++ r₁ = codeDone e ++ r₂) : d = e ∧ r₁ = r₂ := by
  cases d with
  | none =>
      cases e with
      | none => exact ⟨rfl, by simpa [codeDone] using h⟩
      | some v => simp [codeDone] at h
  | some v =>
      cases e with
      | none => simp [codeDone] at h
      | some v' =>
          simp only [codeDone, List.cons_append, List.nil_append, List.cons.injEq,
            true_and] at h
          exact ⟨by rw [h.1], h.2⟩

theorem enc_injective : Function.Injective enc := by
  intro σ τ h
  rcases σ with ⟨st, tg, ac, es, inn, stk, dn⟩
  rcases τ with ⟨st', tg', ac', es', inn', stk', dn'⟩
  simp only [enc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := codeN_app_inj _ _ _ _ h
  obtain ⟨h2, h⟩ := codeW_app_inj _ _ _ _ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨h3, h4, h⟩ := h
  obtain ⟨h5, h⟩ := codeDone_app_inj _ _ _ _ h
  obtain ⟨h6, h⟩ := codeInner_app_inj _ _ _ _ h
  have h7 : stk = stk' := (codeStack_app_inj stk stk' [] [] (by simpa using h)).1
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
  rfl

theorem enc_ne_nil (σ : SState) : enc σ ≠ [] := by
  simp only [enc]
  cases σ.stage <;> simp [codeN]

open Classical in
/-- The decoding function: the inverse of `enc` where defined. -/
noncomputable def dec (m : Word) : SState :=
  if h : ∃ σ, enc σ = m then h.choose else initState

theorem dec_enc (σ : SState) : dec (enc σ) = σ := by
  have h : ∃ τ, enc τ = enc σ := ⟨σ, rfl⟩
  simp only [dec, dif_pos h]
  exact enc_injective h.choose_spec

theorem dec_nil : dec [] = initState := by
  have h : ¬ ∃ σ, enc σ = [] := by
    rintro ⟨σ, hσ⟩
    exact enc_ne_nil σ hσ
  simp only [dec, dif_neg h]

/-! ## Lengths -/

@[simp] theorem codeN_length (n : ℕ) : (codeN n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [codeN, ih]

@[simp] theorem codeW_length (w : Word) : (codeW w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b t ih => simp [codeW, ih]; omega

theorem codeFrame_length (f : Frame) :
    (codeFrame f).length = f.k + 2 * f.a.length + 2 * f.b.length + 2 * f.mid.length + 5 := by
  simp only [codeFrame, List.length_append, codeN_length, codeW_length, List.length_cons,
    List.length_nil]
  omega

/-! ## The invariant -/

theorem univNext_length {s : ℕ} {w m : Word} (h : univNext s w = some m) : m.length ≤ s := by
  unfold univNext at h
  split at h
  · rename_i hle
    cases h
    exact hle
  · exact absurd h (by simp)

/-- `StackOK stage l k` : `l` is a well-formed recursion stack for a pending computation of
level `k`, all of whose data fit in words of length at most `stage`. -/
def StackOK (stage : ℕ) : List Frame → ℕ → Prop
  | [], k => k ≤ stage + 1
  | f :: t, k =>
      f.k = k ∧ f.a.length ≤ stage ∧ f.b.length ≤ stage ∧ f.mid.length ≤ stage ∧
        StackOK stage t (k + 1)

/-- A stack which is well formed for the level of its top frame. -/
def StackTopOK (stage : ℕ) : List Frame → Prop
  | [] => True
  | f :: t => StackOK stage (f :: t) f.k

theorem StackOK.length_add_le {stage : ℕ} :
    ∀ (l : List Frame) (k : ℕ), StackOK stage l k → l.length + k ≤ stage + 1 := by
  intro l
  induction l with
  | nil => intro k h; simpa using h
  | cons f t ih =>
      intro k h
      have := ih (k + 1) h.2.2.2.2
      simp only [List.length_cons]
      omega

theorem StackOK.frame_bounds {stage : ℕ} :
    ∀ (l : List Frame) (k : ℕ), StackOK stage l k → ∀ f ∈ l,
      f.k ≤ stage + 1 ∧ f.a.length ≤ stage ∧ f.b.length ≤ stage ∧ f.mid.length ≤ stage := by
  intro l
  induction l with
  | nil => intro k h f hf; simp at hf
  | cons g t ih =>
      intro k h f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · obtain ⟨hk, hb1, hb2, hb3, hrest⟩ := h
        have hlen := StackOK.length_add_le t (k + 1) hrest
        exact ⟨by omega, hb1, hb2, hb3⟩
      · exact ih (k + 1) h.2.2.2.2 f hf

theorem StackOK.top {stage : ℕ} {l : List Frame} {k : ℕ} (h : StackOK stage l k) :
    StackTopOK stage l := by
  cases l with
  | nil => trivial
  | cons f t =>
      have hk : f.k = k := h.1
      show StackOK stage (f :: t) f.k
      rw [hk]
      exact h

theorem StackTopOK.length_le {stage : ℕ} {l : List Frame} (h : StackTopOK stage l) :
    l.length ≤ stage + 1 := by
  cases l with
  | nil => simp
  | cons f t =>
      have := StackOK.length_add_le (f :: t) f.k h
      omega

theorem StackTopOK.frame_bounds {stage : ℕ} {l : List Frame} (h : StackTopOK stage l) :
    ∀ f ∈ l, f.k ≤ stage + 1 ∧ f.a.length ≤ stage ∧ f.b.length ≤ stage ∧ f.mid.length ≤ stage := by
  cases l with
  | nil => intro f hf; simp at hf
  | cons f t => exact StackOK.frame_bounds (f :: t) f.k h

/-- The invariant maintained by the simulator. -/
def Inv (σ : SState) : Prop :=
  σ.target.length ≤ σ.stage ∧
    (match σ.inner with
      | Inner.call k a b =>
          a.length ≤ σ.stage ∧ b.length ≤ σ.stage ∧ StackOK σ.stage σ.stack k
      | Inner.ret _ => StackTopOK σ.stage σ.stack)

theorem Inv_initState : Inv initState := by
  refine ⟨by simp [initState], ?_⟩
  exact ⟨by simp [initState], by simp [initState], by simp [initState, StackOK]⟩

theorem Inv.stack_top {σ : SState} (h : Inv σ) : StackTopOK σ.stage σ.stack := by
  obtain ⟨-, h2⟩ := h
  revert h2
  cases hi : σ.inner with
  | call k a b => intro h2; exact h2.2.2.top
  | ret v => intro h2; exact h2

theorem Inv.stack_length {σ : SState} (h : Inv σ) : σ.stack.length ≤ σ.stage + 1 :=
  h.stack_top.length_le

theorem Inv.frame_bounds {σ : SState} (h : Inv σ) : ∀ f ∈ σ.stack,
    f.k ≤ σ.stage + 1 ∧ f.a.length ≤ σ.stage ∧ f.b.length ≤ σ.stage ∧ f.mid.length ≤ σ.stage :=
  h.stack_top.frame_bounds

theorem Inv.inner_length {σ : SState} (h : Inv σ) :
    (codeInner σ.inner).length ≤ 5 * σ.stage + 5 := by
  obtain ⟨-, h2⟩ := h
  revert h2
  cases hi : σ.inner with
  | call k a b =>
      intro h2
      obtain ⟨ha, hb, hst⟩ := h2
      have hk : k ≤ σ.stage + 1 := by
        have := StackOK.length_add_le σ.stack k hst
        omega
      simp only [codeInner, List.length_cons, List.length_append, codeN_length, codeW_length]
      omega
  | ret v => intro _; simp [codeInner]

/-! ## The length of an encoded state -/

theorem codeStack_length_le (stage : ℕ) :
    ∀ (l : List Frame),
      (∀ f ∈ l, f.k ≤ stage + 1 ∧ f.a.length ≤ stage ∧ f.b.length ≤ stage ∧
        f.mid.length ≤ stage) →
      (codeStack l).length ≤ 1 + l.length * (7 * stage + 8) := by
  intro l
  induction l with
  | nil => intro _; simp [codeStack]
  | cons f t ih =>
      intro hb
      have hf := hb f (by simp)
      have ht := ih (fun g hg => hb g (by simp [hg]))
      have hcf : (codeFrame f).length ≤ 7 * stage + 6 := by
        rw [codeFrame_length]; omega
      simp only [codeStack, List.length_cons, List.length_append]
      rw [add_mul, one_mul]
      generalize hX : t.length * (7 * stage + 8) = X at ht ⊢
      omega

theorem enc_length_le {σ : SState} (h : Inv σ) :
    (enc σ).length ≤ 25 * (σ.stage + 1) ^ 2 := by
  have h1 : (codeW σ.target).length ≤ 2 * σ.stage + 1 := by
    rw [codeW_length]
    have := h.1
    omega
  have h2 : (codeDone σ.done).length ≤ 2 := by
    cases σ.done <;> simp [codeDone]
  have h3 := h.inner_length
  have h4 : (codeStack σ.stack).length ≤ 1 + (σ.stage + 1) * (7 * σ.stage + 8) := by
    have hb := codeStack_length_le σ.stage σ.stack h.frame_bounds
    have hl : σ.stack.length ≤ σ.stage + 1 := h.stack_length
    have : σ.stack.length * (7 * σ.stage + 8) ≤ (σ.stage + 1) * (7 * σ.stage + 8) :=
      Nat.mul_le_mul_right _ hl
    omega
  have hexp : (σ.stage + 1) * (7 * σ.stage + 8) = 7 * (σ.stage * σ.stage) + 15 * σ.stage + 8 := by
    ring
  have hsq : 25 * (σ.stage + 1) ^ 2 = 25 * (σ.stage * σ.stage) + 50 * σ.stage + 25 := by
    ring
  simp only [enc, List.length_append, codeN_length, List.length_cons, List.length_nil]
  rw [hexp] at h4
  rw [hsq]
  generalize σ.stage * σ.stage = Q at h4 ⊢
  omega

/-! ## Preservation of the invariant -/

theorem Inv_advanceMid {stage : ℕ} {target : Word} {acc esc v : Bool} {done : Option Bool}
    {fr : Frame} {rest : List Frame}
    (htg : target.length ≤ stage) (hfa : fr.a.length ≤ stage) (hfb : fr.b.length ≤ stage)
    (hrest : StackOK stage rest (fr.k + 1)) :
    Inv (advanceMid ⟨stage, target, acc, esc, Inner.ret v, fr :: rest, done⟩ fr rest) := by
  simp only [advanceMid]
  rcases hu : univNext stage fr.mid with _ | m'
  · exact ⟨htg, hrest.top⟩
  · exact ⟨htg, hfa, univNext_length hu, rfl, hfa, hfb, univNext_length hu, hrest⟩

theorem Inv_sstepAux (M : NMachine) (bit : Option Bool) (σ : SState) (h : Inv σ) :
    Inv (sstepAux M bit σ) := by
  rcases σ with ⟨stage, target, acc, esc, inner, stack, done⟩
  obtain ⟨htg, hin⟩ := h
  simp only at htg hin
  cases inner with
  | call k a b =>
      obtain ⟨ha, hb, hst⟩ := hin
      cases k with
      | zero => exact ⟨htg, hst.top⟩
      | succ k =>
          simp only [sstepAux]
          by_cases hab : a = b
          · rw [if_pos hab]
            exact ⟨htg, hst.top⟩
          · rw [if_neg hab]
            exact ⟨htg, ha, by simp, rfl, ha, hb, by simp, hst⟩
  | ret v =>
      cases stack with
      | nil =>
          simp only [sstepAux]
          rcases hu : univNext stage target with _ | t'
          · split_ifs
            · exact ⟨htg, trivial⟩
            · exact ⟨by simp, by simp, by simp, by simp [StackOK]⟩
            · exact ⟨htg, trivial⟩
          · exact ⟨univNext_length hu, by simp, univNext_length hu, by simp [StackOK]⟩
      | cons fr rest =>
          obtain ⟨hk, hfa, hfb, hfm, hrest⟩ := hin
          simp only [sstepAux]
          by_cases h2 : fr.second = true
          · rw [if_pos h2]
            by_cases hv : v = true
            · rw [if_pos hv]
              exact ⟨htg, hrest.top⟩
            · rw [if_neg hv]
              exact Inv_advanceMid htg hfa hfb hrest
          · rw [if_neg h2]
            by_cases hv : v = true
            · rw [if_pos hv]
              exact ⟨htg, hfm, hfb, rfl, hfa, hfb, hfm, hrest⟩
            · rw [if_neg hv]
              exact Inv_advanceMid htg hfa hfb hrest

theorem Inv_sstep (M : NMachine) (bit : Option Bool) (σ : SState) (h : Inv σ) :
    Inv (sstep M bit σ) := by
  by_cases hd : σ.done = none
  · rw [sstep, if_pos hd]
    exact Inv_sstepAux M bit σ h
  · rw [sstep, if_neg hd]
    exact h

theorem Inv_dstep (M : NMachine) (x : Word) (σ : SState) (h : Inv σ) : Inv (dstep M x σ) :=
  Inv_sstep M _ σ h

theorem Inv_dstepIter (M : NMachine) (x : Word) (t : ℕ) (σ : SState) (h : Inv σ) :
    Inv (dstepIter M x t σ) := by
  induction t generalizing σ with
  | zero => exact h
  | succ t ih => rw [dstepIter_succ]; exact ih _ (Inv_dstep M x σ h)

end Savitch
end CS

/-
# The configuration graph of a nondeterministic machine

For a fixed input `x`, one step of `M` is a relation on words, `edgeB M x`, and the
configurations reachable by `M` are exactly the words reachable in the corresponding graph.
This file relates `savR` (the Savitch recursion) to `M.Reach`.
-/
import RequestProject.Savitch.Sim

namespace CS
namespace Savitch

/-- One step of `M` on input `x`, as a Boolean valued edge relation. -/
def edgeB (M : NMachine) (x : Word) (a b : Word) : Bool :=
  (M.verdict a == none) && decide (b ∈ M.next a x[M.ask a]?)

theorem leafEdge_eq (M : NMachine) (x : Word) (a b : Word) :
    leafEdge M x[M.ask a]? a b = edgeB M x a b := rfl

theorem edgeB_iff {M : NMachine} {x a b : Word} :
    edgeB M x a b = true ↔ M.StepRel x a b := by
  simp [edgeB, NMachine.StepRel]

theorem edgeB_of_stepRel {M : NMachine} {x a b : Word} (h : M.StepRel x a b) :
    edgeB M x a b = true := edgeB_iff.2 h

/-- A path in the configuration graph is a computation of `M`. -/
theorem reach_of_path {M : NMachine} {x : Word} {s n : ℕ} {a b : Word}
    (hp : PathN (edgeB M x) s n a b) (ha : M.Reach x a) : M.Reach x b := by
  induction n generalizing b with
  | zero => rw [PathN.zero_iff] at hp; exact hp ▸ ha
  | succ n ih =>
      obtain ⟨p, hp0, hp1, hstep⟩ := hp
      have hprev : PathN (edgeB M x) s n a (p n) := ⟨p, hp0, rfl, fun i hi => hstep i (by omega)⟩
      have hR : M.Reach x (p n) := ih hprev
      have hE := (hstep n (by omega)).2
      rw [hp1] at hE
      exact hR.tail (edgeB_iff.1 hE)

/-- The predicate tested by the accepting scan of the simulator. -/
def accP (M : NMachine) (x : Word) (stage : ℕ) (c : Word) : Bool :=
  savR (edgeB M x) stage (stage + 1) [] c && (M.verdict c == some true)

/-- The predicate tested by the "does the computation leave the current space bound" scan. -/
def escP (M : NMachine) (x : Word) (stage : ℕ) (c : Word) : Bool :=
  savR (edgeB M x) stage (stage + 1) [] c && escapes M x[M.ask c]? stage c

theorem reach_of_savR {M : NMachine} {x : Word} {stage : ℕ} {c : Word}
    (hc : c.length ≤ stage) (h : savR (edgeB M x) stage (stage + 1) [] c = true) :
    M.Reach x c := by
  obtain ⟨n, hp⟩ := (savR_reach_iff (edgeB M x) stage (by simp) hc).1 h
  exact reach_of_path hp (M.reach_refl x)

theorem accP_sound {M : NMachine} {x : Word} {stage : ℕ} {c : Word}
    (hc : c.length ≤ stage) (h : accP M x stage c = true) : x ∈ M.lang := by
  rw [accP, Bool.and_eq_true] at h
  refine ⟨c, reach_of_savR hc h.1, ?_⟩
  simpa using h.2

/-- At a stage which is at least the true space bound, no reachable configuration can leave
the set of words of length at most `stage`. -/
theorem escP_eq_false_of_bound {M : NMachine} {x : Word} {S : ℕ}
    (hS : ∀ c, M.Reach x c → c.length ≤ S) (c : Word) (hc : c.length ≤ S) :
    escP M x S c = false := by
  by_contra h
  rw [Bool.not_eq_false, escP, Bool.and_eq_true] at h
  obtain ⟨hsav, hesc⟩ := h
  have hreach : M.Reach x c := reach_of_savR hc hsav
  rw [escapes, Bool.and_eq_true, List.any_eq_true] at hesc
  obtain ⟨hv, c', hc', hlen⟩ := hesc
  have hstep : M.StepRel x c c' := ⟨by simpa using hv, hc'⟩
  have := hS c' (hreach.tail hstep)
  simp only [decide_eq_true_eq] at hlen
  omega

/-- If no reachable configuration escapes the current stage, then the Savitch recursion at that
stage is complete: it finds every reachable configuration. -/
theorem savR_complete_of_no_escape {M : NMachine} {x : Word} {stage : ℕ}
    (hX : ∀ u : Word, u.length ≤ stage → escP M x stage u = false) :
    ∀ c, M.Reach x c → c.length ≤ stage ∧ savR (edgeB M x) stage (stage + 1) [] c = true := by
  intro c hc
  induction hc with
  | refl => exact ⟨by simp, by simp [savR_succ]⟩
  | @tail c₁ c₂ hab hstep ih =>
      obtain ⟨hlen, hsav⟩ := ih
      have hesc : escapes M x[M.ask c₁]? stage c₁ = false := by
        have h0 := hX c₁ hlen
        simpa [escP, hsav] using h0
      have hlen2 : c₂.length ≤ stage := by
        by_contra hcon
        rw [escapes, Bool.and_eq_false_iff] at hesc
        rcases hesc with h | h
        · rw [beq_eq_false_iff_ne] at h
          exact h hstep.1
        · rw [List.any_eq_false] at h
          have := h c₂ hstep.2
          simp only [decide_eq_true_eq] at this
          omega
      refine ⟨hlen2, ?_⟩
      obtain ⟨n, hp⟩ := (savR_reach_iff (edgeB M x) stage (by simp) hlen).1 hsav
      have hp2 : PathN (edgeB M x) stage (n + 1) [] c₂ :=
        hp.comp (PathN.single hlen (edgeB_of_stepRel hstep)) hlen
      exact (savR_reach_iff (edgeB M x) stage (by simp) hlen2).2 ⟨n + 1, hp2⟩

end Savitch
end CS

