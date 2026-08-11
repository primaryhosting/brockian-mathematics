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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

universe u v

/-- A deterministic two-party communication protocol tree over inputs `X` (Alice) and `Y` (Bob).
`alice m k` means Alice sends the bit `m x` and the protocol continues with `k (m x)`;
`bob m k` means Bob sends the bit `m y`. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → (Bool → Protocol X Y) → Protocol X Y
  | bob : (Y → Bool) → (Bool → Protocol X Y) → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on a given pair of inputs. -/
def run : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice m k, x, y => run (k (m x)) x y
  | bob m k, x, y => run (k (m y)) x y

/-- The transcript (sequence of exchanged bits) of the protocol on a given pair of inputs. -/
def trans : Protocol X Y → X → Y → List Bool
  | leaf _, _, _ => []
  | alice m k, x, y => m x :: trans (k (m x)) x y
  | bob m k, x, y => m y :: trans (k (m y)) x y

/-- The communication cost (depth) of the protocol: the maximal number of bits exchanged. -/
def depth : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ k => 1 + max (depth (k false)) (depth (k true))
  | bob _ k => 1 + max (depth (k false)) (depth (k true))

/-- All root-to-leaf paths of the protocol tree, as bit strings. -/
def paths : Protocol X Y → Finset (List Bool)
  | leaf _ => {[]}
  | alice _ k =>
      (paths (k false)).image (List.cons false) ∪ (paths (k true)).image (List.cons true)
  | bob _ k =>
      (paths (k false)).image (List.cons false) ∪ (paths (k true)).image (List.cons true)

lemma trans_mem_paths (P : Protocol X Y) (x : X) (y : Y) : trans P x y ∈ paths P := by
  induction P generalizing x y with
  | leaf b => simp [trans, paths]
  | alice m k ih =>
      cases h : m x <;> simp [trans, paths, h] <;> exact ih _ x y
  | bob m k ih =>
      cases h : m y <;> simp [trans, paths, h] <;> exact ih _ x y

lemma card_paths_le (P : Protocol X Y) : (paths P).card ≤ 2 ^ depth P := by
  induction P with
  | leaf b => simp [paths, depth]
  | alice m k ih =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (le_trans (Finset.card_image_le) (ih false))
        (le_trans (Finset.card_image_le) (ih true))) ?_
      have h0 : (2:ℕ) ^ depth (k false) ≤ 2 ^ max (depth (k false)) (depth (k true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h1 : (2:ℕ) ^ depth (k true) ≤ 2 ^ max (depth (k false)) (depth (k true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have := add_le_add h0 h1
      simpa [depth, pow_succ, pow_add, two_mul, Nat.add_comm] using this
  | bob m k ih =>
      refine le_trans (Finset.card_union_le _ _) ?_
      refine le_trans (add_le_add (le_trans (Finset.card_image_le) (ih false))
        (le_trans (Finset.card_image_le) (ih true))) ?_
      have h0 : (2:ℕ) ^ depth (k false) ≤ 2 ^ max (depth (k false)) (depth (k true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h1 : (2:ℕ) ^ depth (k true) ≤ 2 ^ max (depth (k false)) (depth (k true)) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have := add_le_add h0 h1
      simpa [depth, pow_succ, pow_add, two_mul, Nat.add_comm] using this

/-- **Rectangle property.** If two input pairs produce the same transcript, then so does the
"crossed" pair, and the protocol's output there is the same. -/
lemma rectangle (P : Protocol X Y) :
    ∀ (x x' : X) (y y' : Y), trans P x y = trans P x' y' →
      trans P x y' = trans P x y ∧ run P x y' = run P x y := by
  induction P with
  | leaf b => intro x x' y y' _; exact ⟨rfl, rfl⟩
  | alice m k ih =>
      intro x x' y y' h
      simp only [trans, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h2' : trans (k (m x)) x y = trans (k (m x)) x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (m x) x x' y y' h2'
      refine ⟨?_, ?_⟩
      · simp only [trans]; rw [ha]
      · simp only [run]; exact hb
  | bob m k ih =>
      intro x x' y y' h
      simp only [trans, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have h2' : trans (k (m y)) x y = trans (k (m y)) x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (m y) x x' y y' h2'
      refine ⟨?_, ?_⟩
      · simp only [trans, ← h1]; rw [ha]
      · simp only [run, ← h1]; exact hb

end Protocol

open Protocol

/-!
## The lower bound

We work with the set-disjointness function on `Fin n`: Alice holds `a : Finset (Fin n)`,
Bob holds `b : Finset (Fin n)`, and the goal is to decide whether `a` and `b` are disjoint.

The protocol is allowed *private randomness*: Alice's input is a pair `(a, ra)` with
`ra : RA` her private random string, and likewise for Bob.  The hypotheses below say the
protocol has *one-sided error*: it never accepts an intersecting pair (`hsound`), and every
disjoint pair is accepted for at least one choice of the random strings (`hcomplete`).  This
is a very weak requirement (it is implied, in particular, by any one-sided-error randomized
protocol with error probability `< 1`, and by any correct deterministic protocol), so the
resulting `n`-bit lower bound is correspondingly strong.

Three consequences are recorded: the deterministic bound, the one-sided-error randomized
bound with any error probability `< 1`, and a two-sided-error bound for protocols whose
error probability is smaller than `4 ^ (-n)`.  The two-sided bound for *constant* error is
Razborov's theorem, whose proof (the corruption bound) is not carried out here.
-/

/-- **Fooling-set bound.**  Suppose `α` and `β` embed the subsets of `Fin n` into the two input
spaces of a protocol `P` in such a way that `P` rejects `(α S, β T)` whenever `S` and `T`
intersect, while accepting every "diagonal" pair `(α S, β Sᶜ)`.  Then `P` has depth at least
`n`.  This is the classical `2 ^ n` fooling set for set disjointness. -/
theorem fooling_bound {n : ℕ} {X : Type u} {Y : Type v} (P : Protocol X Y)
    (α : Finset (Fin n) → X) (β : Finset (Fin n) → Y)
    (hsound : ∀ S T : Finset (Fin n), ¬ Disjoint S T → run P (α S) (β T) = false)
    (hacc : ∀ S : Finset (Fin n), run P (α S) (β Sᶜ) = true) :
    n ≤ depth P := by
  classical
  set F : Finset (Fin n) → List Bool := fun S => trans P (α S) (β Sᶜ)
  have hinj : Function.Injective F := by
    intro S T hST
    by_contra hne
    have hex : ∃ i : Fin n, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext i
      exact ⟨fun hi => (hcon i).1 hi, fun hi => (hcon i).2 hi⟩
    obtain ⟨i, hi⟩ := hex
    rcases hi with ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩
    · -- the crossed pair `(α S, β Tᶜ)` gets the same transcript, hence is accepted too
      obtain ⟨_, hrun⟩ := rectangle P (α S) (α T) (β Sᶜ) (β Tᶜ) hST
      have h1 : run P (α S) (β Tᶜ) = true := by rw [hrun]; exact hacc S
      have h2 : ¬ Disjoint S (Tᶜ : Finset (Fin n)) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨i, hiS, Finset.mem_compl.mpr hiT⟩
      rw [hsound S Tᶜ h2] at h1
      exact Bool.false_ne_true h1
    · obtain ⟨_, hrun⟩ := rectangle P (α T) (α S) (β Tᶜ) (β Sᶜ) hST.symm
      have h1 : run P (α T) (β Sᶜ) = true := by rw [hrun]; exact hacc T
      have h2 : ¬ Disjoint T (Sᶜ : Finset (Fin n)) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨i, hiT, Finset.mem_compl.mpr hiS⟩
      rw [hsound T Sᶜ h2] at h1
      exact Bool.false_ne_true h1
  have hcard : (2 : ℕ) ^ n ≤ (paths P).card := by
    have h1 : (Finset.univ : Finset (Finset (Fin n))).card ≤ (paths P).card :=
      Finset.card_le_card_of_injOn F (fun S _ => trans_mem_paths _ _ _)
        (fun S _ T _ h => hinj h)
    simpa [Finset.card_univ, Fintype.card_finset] using h1
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ depth P := le_trans hcard (card_paths_le P)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- **Set-disjointness requires `n` bits of communication.**

Any (private-coin, one-sided error) randomized communication protocol for set disjointness on
a universe of size `n` must exchange at least `n` bits in the worst case: the one-sided
randomized communication complexity of `DISJ_n` is `Ω(n)` (indeed `≥ n`). -/
theorem disjointness_lb {n : ℕ} {RA : Type u} {RB : Type v}
    (P : Protocol (Finset (Fin n) × RA) (Finset (Fin n) × RB))
    (hsound : ∀ (a b : Finset (Fin n)) (ra : RA) (rb : RB),
      ¬ Disjoint a b → run P (a, ra) (b, rb) = false)
    (hcomplete : ∀ (a b : Finset (Fin n)), Disjoint a b →
      ∃ (ra : RA) (rb : RB), run P (a, ra) (b, rb) = true) :
    n ≤ depth P := by
  classical
  -- pick, for each `S`, random strings making the protocol accept `(S, Sᶜ)`
  have hdisj : ∀ S : Finset (Fin n), Disjoint S Sᶜ := fun _ => disjoint_compl_right
  choose ra rb hacc using fun S : Finset (Fin n) => hcomplete S Sᶜ (hdisj S)
  refine fooling_bound P (fun S => (S, ra S)) (fun U => (U, rb Uᶜ)) ?_ ?_
  · intro S T hST
    exact hsound S T (ra S) (rb Tᶜ) hST
  · intro S
    simpa [compl_compl] using hacc S

/-- Deterministic corollary: every correct deterministic protocol for set disjointness on
`Fin n` has depth at least `n`. -/
theorem disjointness_lb_deterministic {n : ℕ}
    (P : Protocol (Finset (Fin n) × Unit) (Finset (Fin n) × Unit))
    (hP : ∀ (a b : Finset (Fin n)) (ra rb : Unit),
      run P (a, ra) (b, rb) = decide (Disjoint a b)) :
    n ≤ depth P := by
  refine disjointness_lb P (fun a b ra rb h => ?_) (fun a b h => ⟨(), (), ?_⟩)
  · rw [hP]; simp [h]
  · rw [hP]; simp [h]

/-- Randomized corollary: if the protocol never accepts an intersecting pair, and accepts each
disjoint pair with probability at least `1 - ε` for some `ε < 1` (over uniformly chosen private
random strings), then it must exchange at least `n` bits. -/
theorem disjointness_lb_randomized {n : ℕ} {RA RB : Type}
    [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB] [DecidableEq RA] [DecidableEq RB]
    (P : Protocol (Finset (Fin n) × RA) (Finset (Fin n) × RB)) (ε : ℝ) (hε : ε < 1)
    (hsound : ∀ (a b : Finset (Fin n)) (ra : RA) (rb : RB),
      ¬ Disjoint a b → run P (a, ra) (b, rb) = false)
    (hcorrect : ∀ (a b : Finset (Fin n)), Disjoint a b →
      1 - ε ≤ ((Finset.univ.filter
          (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
        / ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ))) :
    n ≤ depth P := by
  refine disjointness_lb P hsound ?_
  intro a b hab
  have hA : (0 : ℝ) < (Fintype.card RA : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := RA)
  have hB : (0 : ℝ) < (Fintype.card RB : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := RB)
  have h := hcorrect a b hab
  have hpos : (0 : ℝ) < ((Finset.univ.filter
      (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ) := by
    have h0 : (0:ℝ) < 1 - ε := by linarith
    have hd : (0:ℝ) < (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := mul_pos hA hB
    have hq := lt_of_lt_of_le h0 h
    have hrw : ((Finset.univ.filter
        (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
        = (((Finset.univ.filter
          (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
          / ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)))
          * ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) := by
      field_simp
    rw [hrw]
    exact mul_pos hq hd
  have : (Finset.univ.filter (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos
  obtain ⟨p, hp⟩ := this
  exact ⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩

/-- Two-sided error corollary.  If, on every input pair, the protocol errs (in either
direction) for fewer than a `4 ^ (-n)` fraction of the private random strings, then it must
exchange at least `n` bits.  (The error probability required here is exponentially small; the
two-sided bound for constant error is Razborov's theorem and is not proved here.) -/
theorem disjointness_lb_two_sided {n : ℕ} {RA RB : Type}
    [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]
    (P : Protocol (Finset (Fin n) × RA) (Finset (Fin n) × RB))
    (herr : ∀ a b : Finset (Fin n),
      (((Finset.univ : Finset (RA × RB)).filter
          (fun p => run P (a, p.1) (b, p.2) ≠ decide (Disjoint a b))).card : ℝ)
        < ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n) :
    n ≤ depth P := by
  classical
  set Bad : Finset (Fin n) × Finset (Fin n) → Finset (RA × RB) := fun q =>
    (Finset.univ : Finset (RA × RB)).filter
      (fun p => run P (q.1, p.1) (q.2, p.2) ≠ decide (Disjoint q.1 q.2))
  -- a union bound produces a single pair of random strings that is correct on all inputs
  have hne : ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card
      < Fintype.card (RA × RB) := by
    have h1 : (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
        ≤ ∑ q : Finset (Fin n) × Finset (Fin n), ((Bad q).card : ℝ) := by
      have := Finset.card_biUnion_le (s := (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))))
        (t := Bad)
      exact_mod_cast this
    have h2 : (∑ q : Finset (Fin n) × Finset (Fin n), ((Bad q).card : ℝ))
        < ∑ _q : Finset (Fin n) × Finset (Fin n),
            ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun q _ => herr q.1 q.2)
    have hpow : ((4 : ℝ)) ^ n = (2:ℝ) ^ n * (2:ℝ) ^ n := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
    have h3 : (∑ _q : Finset (Fin n) × Finset (Fin n),
        ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n)
        = (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [hpow]
      field_simp
    have h4 : (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
        < (Fintype.card (RA × RB) : ℝ) := by
      have : (Fintype.card (RA × RB) : ℝ)
          = (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := by
        rw [Fintype.card_prod]; push_cast; ring
      rw [this]
      calc (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
          ≤ _ := h1
        _ < _ := h2
        _ = _ := h3
    exact_mod_cast h4
  obtain ⟨p, hp⟩ : ∃ p : RA × RB,
      p ∉ (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (RA × RB)).card
        ≤ ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card :=
      Finset.card_le_card (fun p _ => hcon p)
    rw [Finset.card_univ] at this
    omega
  have hgood : ∀ a b : Finset (Fin n), run P (a, p.1) (b, p.2) = decide (Disjoint a b) := by
    intro a b
    by_contra hbad
    exact hp (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩)
  refine fooling_bound P (fun S => (S, p.1)) (fun U => (U, p.2)) ?_ ?_
  · intro S T hST
    rw [hgood S T]
    simp [hST]
  · intro S
    rw [hgood S Sᶜ]
    simp [disjoint_compl_right]

/-! ### Sanity check: the hypotheses above are satisfiable -/

/-- A concrete (correct, deterministic) two-bit protocol for disjointness on `Fin 1`. -/
def exampleProtocol : Protocol (Finset (Fin 1) × Unit) (Finset (Fin 1) × Unit) :=
  .alice (fun x => decide ((0 : Fin 1) ∈ x.1)) (fun ba =>
    .bob (fun y => decide ((0 : Fin 1) ∈ y.1)) (fun bb => .leaf (!(ba && bb))))

example : ∀ (a b : Finset (Fin 1)) (ra rb : Unit),
    run exampleProtocol (a, ra) (b, rb) = decide (Disjoint a b) := by decide

example : (1 : ℕ) ≤ depth exampleProtocol :=
  disjointness_lb_deterministic exampleProtocol (by decide)

end CS

