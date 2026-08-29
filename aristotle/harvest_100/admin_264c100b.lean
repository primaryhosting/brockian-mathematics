import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by decide +revert

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by decide +revert

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with h0 | h1
  · exact absurd h0 h
  · exact h1

lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert h; revert a b; decide

lemma add_self_cube {n : ℕ} (x : V n) : x + x = 0 := by
  funext i
  simpa using zmod2_add_self (x i)

lemma add_add_cancel_cube {n : ℕ} (x s : V n) : x + s + s = x := by
  rw [add_assoc, add_self_cube, add_zero]

/-- The standard `𝔽₂`-bilinear form on `(ℤ/2)ⁿ`. -/
def dotp {n : ℕ} (x y : V n) : ZMod 2 := ∑ i, x i * y i

lemma dotp_comm {n : ℕ} (x y : V n) : dotp x y = dotp y x := by
  simp [dotp, mul_comm]

lemma dotp_add_left {n : ℕ} (x y z : V n) : dotp (x + y) z = dotp x z + dotp y z := by
  simp [dotp, add_mul, Finset.sum_add_distrib]

lemma dotp_zero_left {n : ℕ} (y : V n) : dotp 0 y = 0 := by
  simp [dotp]

lemma dotp_zero_right {n : ℕ} (x : V n) : dotp x 0 = 0 := by
  simp [dotp]

/-! ## The quantum side: interference in Simon's algorithm

After the oracle call and the measurement of the second register, the first register of
Simon's algorithm carries the uniform superposition over the coset `{x₀, x₀ + s}`.
Applying the Hadamard transform and measuring yields an outcome `y`, and the two lemmas
below say exactly that this outcome is *uniformly distributed over the hyperplane*
`s^⊥ = {y | ⟪s, y⟫ = 0}`: outcomes with `⟪s, y⟫ = 1` have amplitude `0`, and each of the
`2ⁿ⁻¹` remaining outcomes has probability `2 / 2ⁿ = 2^{-(n-1)}`. -/

/-- The character `a ↦ (-1)ᵃ` of `ℤ/2`. -/
noncomputable def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;> subst ha <;>
    subst hb <;> simp [sgn, h11, h10]

lemma norm_sgn (a : ZMod 2) : ‖sgn a‖ = 1 := by
  rcases zmod2_cases a with ha | ha <;> subst ha <;> simp [sgn]

/-- The `n`-qubit Hadamard (Fourier) transform on `(ℤ/2)ⁿ`. -/
noncomputable def hadamard {n : ℕ} (g : V n → ℂ) (y : V n) : ℂ :=
  (Real.sqrt (2 ^ n))⁻¹ * ∑ x, sgn (dotp x y) * g x

/-- The state of the first register of Simon's algorithm after measuring the second
register: the uniform superposition over the coset `{x₀, x₀ + s}`. -/
noncomputable def simonState {n : ℕ} (s x0 : V n) : V n → ℂ :=
  fun x => if x ∈ ({x0, x0 + s} : Finset (V n)) then (Real.sqrt 2)⁻¹ else 0

lemma hadamard_simonState {n : ℕ} (s x0 y : V n) (hs : s ≠ 0) :
    hadamard (simonState s x0) y =
      (Real.sqrt (2 ^ n))⁻¹ * ((Real.sqrt 2)⁻¹ * (sgn (dotp x0 y) + sgn (dotp (x0 + s) y))) := by
  have hne : x0 ≠ x0 + s := fun h => hs (left_eq_add.mp h)
  have hterm : ∀ x : V n, sgn (dotp x y) * simonState s x0 x
      = if x ∈ ({x0, x0 + s} : Finset (V n)) then sgn (dotp x y) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else 0 := by
    intro x
    unfold simonState
    split_ifs <;> simp
  unfold hadamard
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  push_cast
  ring

/-- **Destructive interference.** Any measurement outcome `y` that is *not* orthogonal to the
hidden shift `s` has amplitude zero. -/
lemma hadamard_simonState_eq_zero {n : ℕ} (s x0 y : V n) (h : dotp s y = 1) :
    hadamard (simonState s x0) y = 0 := by
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, dotp_zero_left] at h
    exact absurd h (by decide)
  rw [hadamard_simonState s x0 y hs, dotp_add_left, h, sgn_add]
  have : sgn 1 = -1 := by norm_num [sgn]
  rw [this]
  ring

/-- **Uniformity on `s^⊥`.** Every outcome `y` orthogonal to `s` is observed with
probability `2 / 2ⁿ`. -/
lemma prob_hadamard_simonState {n : ℕ} (s x0 y : V n) (hs : s ≠ 0) (h : dotp s y = 0) :
    ‖hadamard (simonState s x0) y‖ ^ 2 = 2 / 2 ^ n := by
  have hsq : Real.sqrt (2 ^ n) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [hadamard_simonState s x0 y hs, dotp_add_left, h, add_zero]
  have hrw : ∀ a : ℂ, (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + a))
      = (((Real.sqrt (2 ^ n))⁻¹ * (Real.sqrt 2)⁻¹ * 2 : ℝ) : ℂ) * a := by
    intro a
    push_cast
    ring
  rw [hrw, norm_mul, norm_sgn, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  field_simp
  nlinarith [hsq, hsq2, hpos, hpos2]

/-! ## `O(n)` samples determine the hidden shift -/

/-- **The post-processing of Simon's algorithm succeeds with `O(n)` samples.**
For every nonzero shift `s` there is a set of at most `n` vectors `Y ⊆ s^⊥` whose common
orthogonal complement is exactly `{0, s}`; hence `n` measurement outcomes suffice to pin
down `s`, i.e. Simon's problem is solved with `O(n)` quantum queries. -/
lemma exists_small_determining_set {n : ℕ} (s : V n) (hs : s ≠ 0) :
    ∃ Y : Finset (V n), Y.card ≤ n ∧ ∀ v : V n, (∀ y ∈ Y, dotp y v = 0) ↔ (v = 0 ∨ v = s) := by
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, s i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hs (funext hcon)
  have hi0' : s i0 = 1 := zmod2_eq_one_of_ne_zero hi0
  set yv : Fin n → V n :=
    fun j i => (if i = j then (1 : ZMod 2) else 0) + (if i = i0 then s j else 0) with hyv
  have key : ∀ (j : Fin n) (v : V n), dotp (yv j) v = v j + s j * v i0 := by
    intro j v
    simp [dotp, hyv, add_mul, Finset.sum_add_distrib, Finset.sum_ite_eq']
  refine ⟨(Finset.univ.erase i0).image yv, ?_, ?_⟩
  · refine le_trans (Finset.card_image_le) ?_
    simp
  · intro v
    constructor
    · intro h
      have hall : ∀ j : Fin n, v j = s j * v i0 := by
        intro j
        by_cases hji : j = i0
        · subst hji; simp [hi0']
        · have hmem : yv j ∈ (Finset.univ.erase i0).image yv :=
            Finset.mem_image_of_mem yv (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
          have := h (yv j) hmem
          rw [key j v] at this
          exact zmod2_eq_of_add_eq_zero this
      rcases zmod2_cases (v i0) with h0 | h1
      · left
        funext j
        rw [hall j, h0, mul_zero]
        rfl
      · right
        funext j
        rw [hall j, h1, mul_one]
    · intro hv y hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      rw [key j v]
      rcases hv with h0 | h0 <;> subst h0
      · simp
      · simp [hi0', zmod2_add_self]

/-! ## The classical side: deterministic query algorithms -/

/-- A deterministic classical query algorithm of depth at most `d`: a decision tree whose
internal nodes query the oracle at a point of `(ℤ/2)ⁿ` and branch on the answer, and whose
leaves output a Boolean verdict. -/
inductive DTree (n : ℕ) : ℕ → Type where
  | leaf : ∀ {d : ℕ}, Bool → DTree n d
  | query : ∀ {d : ℕ}, V n → (V n → DTree n d) → DTree n (d + 1)

/-- The verdict of the algorithm on the oracle `f`. -/
def DTree.run {n : ℕ} : {d : ℕ} → DTree n d → (V n → V n) → Bool
  | _, .leaf b, _ => b
  | _, .query v k, f => DTree.run (k (f v)) f

/-- The set of points actually queried by the algorithm when run on the oracle `f`. -/
def DTree.queries {n : ℕ} : {d : ℕ} → DTree n d → (V n → V n) → Finset (V n)
  | _, .leaf _, _ => ∅
  | _, .query v k, f => insert v (DTree.queries (k (f v)) f)

lemma DTree.card_queries_le {n : ℕ} : ∀ {d : ℕ} (T : DTree n d) (f : V n → V n),
    (T.queries f).card ≤ d := by
  intro d T
  induction T with
  | leaf b => intro f; simp [DTree.queries]
  | query v k ih =>
      intro f
      have h1 : (insert v ((k (f v)).queries f)).card ≤ ((k (f v)).queries f).card + 1 :=
        Finset.card_insert_le _ _
      have h2 := ih (f v) f
      simp only [DTree.queries]
      omega

/-- Two oracles agreeing on all points queried produce the same run and the same queries. -/
lemma DTree.run_queries_congr {n : ℕ} : ∀ {d : ℕ} (T : DTree n d) (f g : V n → V n),
    (∀ x ∈ T.queries f, g x = f x) → T.queries g = T.queries f ∧ T.run g = T.run f := by
  intro d T
  induction T with
  | leaf b => intro f g _; exact ⟨rfl, rfl⟩
  | query v k ih =>
      intro f g h
      have hv : g v = f v := h v (by simp [DTree.queries])
      have hsub : ∀ x ∈ (k (f v)).queries f, g x = f x := by
        intro x hx
        exact h x (by simp [DTree.queries, hx])
      have := ih (f v) f g hsub
      constructor
      · simp only [DTree.queries, hv]
        rw [this.1]
      · simp only [DTree.run, hv]
        exact this.2

/-- Two oracles agreeing on all points queried produce the same run. -/
lemma DTree.run_congr {n : ℕ} {d : ℕ} (T : DTree n d) (f g : V n → V n)
    (h : ∀ x ∈ T.queries f, g x = f x) : T.run g = T.run f :=
  (DTree.run_queries_congr T f g h).2

/-- `f` is two-to-one with hidden shift `s`. -/
def IsShift {n : ℕ} (f : V n → V n) (s : V n) : Prop :=
  ∀ x y : V n, f x = f y ↔ (y = x ∨ y = x + s)

/-- The algorithm solves Simon's (decision) problem: it says `false` on every one-to-one
oracle and `true` on every two-to-one oracle with a nonzero hidden shift. -/
def Solves {n d : ℕ} (T : DTree n d) : Prop :=
  (∀ f : V n → V n, Function.Injective f → T.run f = false) ∧
  (∀ (f : V n → V n) (s : V n), s ≠ 0 → IsShift f s → T.run f = true)

/-- The two-to-one oracle with hidden shift `s` built by the adversary: it agrees with the
identity on the queried set `Q` (which contains no two points differing by `s`). -/
noncomputable def adversaryOracle {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n) :
    V n → V n :=
  fun x => if x ∈ Q then x else if x + s ∈ Q then x + s else if x i0 = 0 then x else x + s

lemma adversaryOracle_mem {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n) {x : V n}
    (hx : x ∈ Q) : adversaryOracle Q s i0 x = x := by
  simp [adversaryOracle, hx]

lemma adversaryOracle_mem_pair {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n) (x : V n) :
    adversaryOracle Q s i0 x = x ∨ adversaryOracle Q s i0 x = x + s := by
  unfold adversaryOracle
  split_ifs <;> simp

lemma adversaryOracle_shift {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n)
    (hi0 : s i0 = 1) (hQ : ∀ a ∈ Q, a + s ∉ Q) (x : V n) :
    adversaryOracle Q s i0 (x + s) = adversaryOracle Q s i0 x := by
  have hcancel : x + s + s = x := add_add_cancel_cube x s
  have hcoord : (x + s) i0 = x i0 + 1 := by simp [hi0]
  unfold adversaryOracle
  by_cases h1 : x ∈ Q
  · have h2 : x + s ∉ Q := hQ x h1
    simp [h1, h2, hcancel]
  · by_cases h2 : x + s ∈ Q
    · simp [h1, h2]
    · have h3 : x + s + s ∉ Q := by rwa [hcancel]
      rcases zmod2_cases (x i0) with h4 | h4
      · have h5 : (x + s) i0 ≠ 0 := by rw [hcoord, h4]; decide
        rw [if_neg h2, if_neg h3, if_neg h5, if_neg h1, if_neg h2, if_pos h4, hcancel]
      · have h5 : (x + s) i0 = 0 := by rw [hcoord, h4]; decide
        have h6 : x i0 ≠ 0 := by rw [h4]; decide
        rw [if_neg h2, if_neg h3, if_pos h5, if_neg h1, if_neg h2, if_neg h6]

lemma adversaryOracle_isShift {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n)
    (hi0 : s i0 = 1) (hQ : ∀ a ∈ Q, a + s ∉ Q) : IsShift (adversaryOracle Q s i0) s := by
  intro x y
  constructor
  · intro hxy
    rcases adversaryOracle_mem_pair Q s i0 x with hx | hx <;>
      rcases adversaryOracle_mem_pair Q s i0 y with hy | hy <;> rw [hx, hy] at hxy
    · exact Or.inl hxy.symm
    · right
      rw [hxy, add_add_cancel_cube]
    · right
      exact hxy.symm
    · left
      exact (add_right_cancel hxy).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (adversaryOracle_shift Q s i0 hi0 hQ x).symm

/-- **The classical lower bound.** Any deterministic classical algorithm solving Simon's
problem on `n` bits must make at least `2^(n/2)` queries. -/
lemma classical_lower_bound {n d : ℕ} (T : DTree n d) (hn : 1 ≤ n) (hT : Solves T) :
    2 ^ (n / 2) ≤ d := by
  by_contra hcon
  push_neg at hcon
  set Q : Finset (V n) := T.queries (id : V n → V n) with hQdef
  have hQcard : Q.card ≤ d := DTree.card_queries_le T id
  set bad : Finset (V n) := insert 0 (Q.offDiag.image (fun p => p.1 + p.2)) with hbaddef
  -- the set of shifts excluded by the queries is too small to exhaust the cube
  have hmm : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbadcard : bad.card < 2 ^ n := by
    have h1 : bad.card ≤ 1 + (Q.card * Q.card - Q.card) := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h2 := Finset.card_image_le (s := Q.offDiag) (f := fun p : V n × V n => p.1 + p.2)
      rw [Finset.offDiag_card] at h2
      omega
    rcases Nat.eq_zero_or_pos Q.card with h0 | h0
    · rw [h0] at h1
      simp at h1
      omega
    · have hle : Q.card * Q.card ≤ d * d := Nat.mul_le_mul hQcard hQcard
      have hlt : d * d < 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_lt_mul'' hcon hcon
      have hself : Q.card ≤ Q.card * Q.card := Nat.le_mul_of_pos_left _ h0
      omega
  obtain ⟨s, hsbad⟩ : ∃ s : V n, s ∉ bad := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset (V n)) ⊆ bad := fun x _ => hall x
    have := Finset.card_le_card hsub
    have hcard : (Finset.univ : Finset (V n)).card = 2 ^ n := by simp
    omega
  have hs0 : s ≠ 0 := by
    intro h
    exact hsbad (by rw [hbaddef, h]; exact Finset.mem_insert_self _ _)
  have hQfree : ∀ a ∈ Q, a + s ∉ Q := by
    intro a ha hb
    refine hsbad ?_
    have hne : a ≠ a + s := fun h => hs0 (left_eq_add.mp h)
    have hmem : (a, a + s) ∈ Q.offDiag := Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩
    have hsum : a + (a + s) = s := by
      rw [← add_assoc, add_self_cube, zero_add]
    rw [hbaddef]
    refine Finset.mem_insert_of_mem ?_
    exact Finset.mem_image.mpr ⟨(a, a + s), hmem, hsum⟩
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, s i = 1 := by
    by_contra hcon2
    push_neg at hcon2
    refine hs0 (funext fun i => ?_)
    rcases zmod2_cases (s i) with h | h
    · exact h
    · exact absurd h (hcon2 i)
  have hrun : T.run (adversaryOracle Q s i0) = T.run id :=
    DTree.run_congr T id (adversaryOracle Q s i0)
      (fun x hx => adversaryOracle_mem Q s i0 hx)
  rw [hT.1 id Function.injective_id,
    hT.2 (adversaryOracle Q s i0) s hs0 (adversaryOracle_isShift Q s i0 hi0 hQfree)] at hrun
  exact Bool.noConfusion hrun

/-- **Non-vacuity of the classical lower bound.**  Simon's problem really is solvable by a
deterministic query algorithm: here, for `n = 1`, by querying both points of the cube and
comparing the answers. -/
lemma exists_solving_tree :
    Solves (DTree.query (n := 1) (d := 1) (0 : V 1)
      (fun a => DTree.query (d := 0) (1 : V 1) (fun b => DTree.leaf (decide (a = b))))) := by
  have h01 : (0 : V 1) ≠ 1 := by
    intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply, Pi.one_apply] at h0
    exact absurd h0 (by decide)
  constructor
  · intro f hf
    simp only [DTree.run, decide_eq_false_iff_not]
    intro hcon
    exact h01 (hf hcon)
  · intro f s hs hshift
    have hs1 : s = 1 := by
      have h : s 0 ≠ 0 := by
        intro h0
        exact hs (funext fun i => by rw [Subsingleton.elim i 0]; exact h0)
      have h1 : s 0 = 1 := zmod2_eq_one_of_ne_zero h
      funext i
      rw [Subsingleton.elim i 0, Pi.one_apply]
      exact h1
    have hfeq : f 0 = f 1 := by
      refine (hshift 0 1).mpr (Or.inr ?_)
      rw [zero_add, hs1]
    simp only [DTree.run, decide_eq_true_iff]
    exact hfeq

/-! ## Main statement -/

/-- **Simon's problem.**

* (1) and (2): the quantum algorithm.  The measurement outcomes of Simon's circuit are
  *uniformly distributed on the hyperplane* `s^⊥` orthogonal to the hidden shift `s`:
  outcomes off that hyperplane have amplitude `0`, and each of the outcomes on it has
  probability `2 / 2ⁿ`.
* (3): `O(n)` such outcomes determine `s` — there is a set of at most `n` vectors whose
  joint orthogonal complement is exactly `{0, s}`.  So `O(n)` quantum queries suffice.
* (4): classically, every deterministic query algorithm solving Simon's problem (deciding
  whether the oracle is one-to-one or two-to-one with a nonzero hidden shift) needs at
  least `2^(n/2)` queries: `Ω(2^{n/2})`. -/
theorem simon_algorithm :
    (∀ (n : ℕ) (s x0 y : V n), dotp s y = 1 → hadamard (simonState s x0) y = 0) ∧
    (∀ (n : ℕ) (s x0 y : V n), s ≠ 0 → dotp s y = 0 →
        ‖hadamard (simonState s x0) y‖ ^ 2 = 2 / 2 ^ n) ∧
    (∀ (n : ℕ) (s : V n), s ≠ 0 →
        ∃ Y : Finset (V n), Y.card ≤ n ∧
          ∀ v : V n, (∀ y ∈ Y, dotp y v = 0) ↔ (v = 0 ∨ v = s)) ∧
    (∀ (n d : ℕ) (T : DTree n d), 1 ≤ n → Solves T → 2 ^ (n / 2) ≤ d) :=
  ⟨fun _ s x0 y h => hadamard_simonState_eq_zero s x0 y h,
   fun _ s x0 y hs h => prob_hadamard_simonState s x0 y hs h,
   fun _ s hs => exists_small_determining_set s hs,
   fun _ _ T hn hT => classical_lower_bound T hn hT⟩

#print axioms QI.simon_algorithm

end QI

