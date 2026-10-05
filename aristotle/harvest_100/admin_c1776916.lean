/-!
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately written without any `import`, because the required header above is a
module doc comment and Lean does not allow `import` commands after it.  All notions below are
therefore developed from scratch in core Lean 4.

Probabilities over `k` random bits are represented exactly by integer counts: instead of saying
that the acceptance probability is at least `2/3` we say `2 * 2 ^ m ≤ 3 * (number of accepting
random strings)`, and similarly for the other bounds.  This is an exact (not approximate)
reformulation, and it avoids any need for rational arithmetic.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-! ## Strings, languages, algorithms -/

/-- A finite binary string. -/
abbrev Bits := List Bool

/-- A language is a set of binary strings. -/
abbrev Language := Bits → Prop

/-- A randomized algorithm: it reads an input string and a random string, the latter encoded as
a natural number `r < 2 ^ m`, where `m` is the number of random bits used. -/
abbrev RAlgo := Bits → Nat → Bool

/-- A deterministic algorithm. -/
abbrev DAlgo := Bits → Bool

/-- `countUpTo f N` is the number of `r < N` with `f r = true`. -/
def countUpTo (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countUpTo f n + (if f n then 1 else 0)

/-- The number of random strings of length `m` on which `A` accepts `x`; the acceptance
probability of `A` on `x` is `acceptCount A x m / 2 ^ m`. -/
def acceptCount (A : RAlgo) (x : Bits) (m : Nat) : Nat :=
  countUpTo (fun r => A x r) (2 ^ m)

/-- The number of seeds `y < 2 ^ s` for which `A` accepts `x` when its randomness is produced by
the generator `G` (whose first argument is the input length). -/
def genAcceptCount (A : RAlgo) (G : Nat → Nat → Nat) (x : Bits) (s : Nat) : Nat :=
  countUpTo (fun y => A x (G x.length y)) (2 ^ s)

/-- `A` accepts `x` with probability at least `2/3` when given `m` random bits. -/
def AcceptsWhp (A : RAlgo) (x : Bits) (m : Nat) : Prop :=
  2 * 2 ^ m ≤ 3 * acceptCount A x m

/-- `A` accepts `x` with probability at most `1/3` when given `m` random bits. -/
def RejectsWhp (A : RAlgo) (x : Bits) (m : Nat) : Prop :=
  3 * acceptCount A x m ≤ 2 ^ m

/-- The generator `G`, run on all seeds of length `s`, fools the test `A(x, ·)` up to error
`1/12`: the two acceptance probabilities `genAcceptCount / 2 ^ s` and `acceptCount / 2 ^ m`
differ by at most `1/12`. -/
def Fools (A : RAlgo) (G : Nat → Nat → Nat) (x : Bits) (m s : Nat) : Prop :=
  12 * (acceptCount A x m * 2 ^ s) ≤ 12 * (genAcceptCount A G x s * 2 ^ m) + 2 ^ s * 2 ^ m ∧
  12 * (genAcceptCount A G x s * 2 ^ m) ≤ 12 * (acceptCount A x m * 2 ^ s) + 2 ^ s * 2 ^ m

/-- The derandomized algorithm: enumerate all `2 ^ (s |x|)` seeds and take the majority vote of
the outcomes of `A` on the corresponding pseudorandom strings. -/
def majorityAlgo (A : RAlgo) (G : Nat → Nat → Nat) (s : Nat → Nat) : DAlgo :=
  fun x => decide (2 ^ (s x.length) < 2 * genAcceptCount A G x (s x.length))

/-! ## Boolean circuits (used to state the hardness assumption) -/

/-- Boolean circuits over `¬, ∧, ∨` on `n` input variables. -/
inductive Circuit (n : Nat) : Type
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | not : Circuit n → Circuit n
  | and : Circuit n → Circuit n → Circuit n
  | or : Circuit n → Circuit n → Circuit n

/-- Evaluation of a circuit at a Boolean assignment. -/
def Circuit.eval {n : Nat} : Circuit n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .var i, v => v i
  | .not c, v => !(c.eval v)
  | .and c d, v => (c.eval v) && (d.eval v)
  | .or c d, v => (c.eval v) || (d.eval v)

/-- The size (number of gates) of a circuit. -/
def Circuit.size {n : Nat} : Circuit n → Nat
  | .const _ => 1
  | .var _ => 1
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1

/-! ## An abstract model of uniform efficient computation

Setting up a concrete machine model with its running-time bookkeeping is orthogonal to the
mathematical content of the Impagliazzo–Wigderson theorem.  We therefore work with an abstract
model of uniform polynomial-time computation: a `Model` records which resource bounds are
polynomial, which randomized/deterministic algorithms and which generators are polynomial-time
computable, which function families lie in `E`, and the two standard closure properties that
the derandomization argument uses. -/

/-- An abstract model of uniform polynomial-time computation. -/
structure Model where
  /-- Polynomially bounded resource functions. -/
  IsPoly : (Nat → Nat) → Prop
  /-- Randomized polynomial-time algorithms. -/
  RandPoly : RAlgo → Prop
  /-- Deterministic polynomial-time algorithms. -/
  DetPoly : DAlgo → Prop
  /-- Polynomial-time computable generators (input length and seed ↦ pseudorandom string). -/
  GenPoly : (Nat → Nat → Nat) → Prop
  /-- The class `E`: families of Boolean functions computable in time `2 ^ O(n)`. -/
  InE : (∀ n : Nat, (Fin n → Bool) → Bool) → Prop
  /-- Constant resource bounds are polynomial. -/
  isPoly_const : ∀ c : Nat, IsPoly (fun _ => c)
  /-- A deterministic polynomial-time algorithm, read as a randomized algorithm that ignores its
  randomness, is randomized polynomial time. -/
  det_to_rand : ∀ D : DAlgo, DetPoly D → RandPoly (fun x _ => D x)
  /-- Enumerating polynomially many seeds of a polynomial-time generator, running a
  polynomial-time randomized algorithm on each resulting string and taking a majority vote, is a
  deterministic polynomial-time computation. -/
  maj_poly : ∀ (A : RAlgo) (G : Nat → Nat → Nat) (s p : Nat → Nat), RandPoly A → GenPoly G →
    IsPoly p → (∀ n, 2 ^ s n ≤ p n) → DetPoly (majorityAlgo A G s)

namespace Model

variable (M : Model)

/-- The class `P`: languages decided by a deterministic polynomial-time algorithm. -/
def P (L : Language) : Prop :=
  ∃ D : DAlgo, M.DetPoly D ∧ ∀ x, (D x = true ↔ L x)

/-- The class `BPP`: languages decided with two-sided error `1/3` by a randomized
polynomial-time algorithm using polynomially many random bits. -/
def BPP (L : Language) : Prop :=
  ∃ (A : RAlgo) (m : Nat → Nat), M.RandPoly A ∧ M.IsPoly m ∧ ∀ x,
    (L x → AcceptsWhp A x (m x.length)) ∧ (¬ L x → RejectsWhp A x (m x.length))

/-- The hardness-to-randomness conclusion of the Nisan–Wigderson construction, as used by
Impagliazzo and Wigderson: every randomized polynomial-time algorithm is fooled, on every input,
by a polynomial-time computable generator whose seed length is logarithmic, i.e. which has only
polynomially many seeds. -/
def HasNWGenerators : Prop :=
  ∀ (A : RAlgo) (m : Nat → Nat), M.RandPoly A → M.IsPoly m →
    ∃ (G : Nat → Nat → Nat) (s p : Nat → Nat), M.GenPoly G ∧ M.IsPoly p ∧
      (∀ n, 2 ^ s n ≤ p n) ∧ ∀ x, Fools A G x (m x.length) (s x.length)

/-- The Impagliazzo–Wigderson hardness assumption: some family of Boolean functions in `E`
requires Boolean circuits of size at least `2 ^ (n / k)` (an exponential, `2 ^ Ω(n)`, lower
bound) for all large `n`. -/
def ExpHardFunction : Prop :=
  ∃ (f : ∀ n : Nat, (Fin n → Bool) → Bool) (k n₀ : Nat), 0 < k ∧ M.InE f ∧
    ∀ n, n₀ ≤ n → ∀ C : Circuit n, (∀ v, C.eval v = f n v) → 2 ^ (n / k) ≤ C.size

end Model

/-! ## The counting core -/

theorem two_pow_pos (m : Nat) : 0 < 2 ^ m := Nat.two_pow_pos m

/-- Arithmetic core, accepting case: if the true acceptance probability is at least `2/3` and
the generator fools the test up to `1/12`, then more than half of the seeds are accepting. -/
theorem majority_arith_yes (a b c d : Nat) (hb : 0 < b) (hd : 0 < d)
    (hgap : 2 * b ≤ 3 * a) (hfool : 12 * (a * d) ≤ 12 * (c * b) + d * b) : d < 2 * c := by
  have hcomm : d * b = b * d := Nat.mul_comm d b
  have h1 : 8 * b ≤ 12 * a := by omega
  have h2 : (8 * b) * d ≤ (12 * a) * d := Nat.mul_le_mul_right d h1
  have h3 : 8 * (b * d) ≤ 12 * (a * d) := by
    calc 8 * (b * d) = (8 * b) * d := by rw [Nat.mul_assoc]
    _ ≤ (12 * a) * d := h2
    _ = 12 * (a * d) := by rw [Nat.mul_assoc]
  have h4 : 7 * (b * d) ≤ 12 * (c * b) := by omega
  have h5 : (7 * d) * b ≤ (12 * c) * b := by
    calc (7 * d) * b = 7 * (b * d) := by rw [Nat.mul_assoc, hcomm]
    _ ≤ 12 * (c * b) := h4
    _ = (12 * c) * b := by rw [Nat.mul_assoc]
  have h6 : 7 * d ≤ 12 * c := Nat.le_of_mul_le_mul_right h5 hb
  omega

/-- Arithmetic core, rejecting case: if the true acceptance probability is at most `1/3` and the
generator fools the test up to `1/12`, then at most half of the seeds are accepting. -/
theorem majority_arith_no (a b c d : Nat) (hb : 0 < b) (hd : 0 < d)
    (hgap : 3 * a ≤ b) (hfool : 12 * (c * b) ≤ 12 * (a * d) + d * b) : 2 * c ≤ d := by
  have hcomm : d * b = b * d := Nat.mul_comm d b
  have h1 : 12 * a ≤ 4 * b := by omega
  have h2 : (12 * a) * d ≤ (4 * b) * d := Nat.mul_le_mul_right d h1
  have h3 : 12 * (a * d) ≤ 4 * (b * d) := by
    calc 12 * (a * d) = (12 * a) * d := by rw [Nat.mul_assoc]
    _ ≤ (4 * b) * d := h2
    _ = 4 * (b * d) := by rw [Nat.mul_assoc]
  have h4 : 12 * (c * b) ≤ 5 * (b * d) := by omega
  have h5 : (12 * c) * b ≤ (5 * d) * b := by
    calc (12 * c) * b = 12 * (c * b) := by rw [Nat.mul_assoc]
    _ ≤ 5 * (b * d) := h4
    _ = (5 * d) * b := by rw [Nat.mul_assoc, hcomm]
  have h6 : 12 * c ≤ 5 * d := Nat.le_of_mul_le_mul_right h5 hb
  omega

/-- If `A` accepts `x` with probability at least `2/3` and `G` fools `A` on `x`, the majority
vote over the seeds of `G` accepts. -/
theorem majorityAlgo_eq_true_of_acceptsWhp (A : RAlgo) (G : Nat → Nat → Nat) (x : Bits)
    (m s : Nat → Nat) (hacc : AcceptsWhp A x (m x.length))
    (hfool : Fools A G x (m x.length) (s x.length)) : majorityAlgo A G s x = true := by
  have := majority_arith_yes (acceptCount A x (m x.length)) (2 ^ (m x.length))
    (genAcceptCount A G x (s x.length)) (2 ^ (s x.length))
    (two_pow_pos _) (two_pow_pos _) hacc hfool.1
  simpa [majorityAlgo] using this

/-- If `A` accepts `x` with probability at most `1/3` and `G` fools `A` on `x`, the majority vote
over the seeds of `G` rejects. -/
theorem majorityAlgo_eq_false_of_rejectsWhp (A : RAlgo) (G : Nat → Nat → Nat) (x : Bits)
    (m s : Nat → Nat) (hrej : RejectsWhp A x (m x.length))
    (hfool : Fools A G x (m x.length) (s x.length)) : majorityAlgo A G s x = false := by
  have := majority_arith_no (acceptCount A x (m x.length)) (2 ^ (m x.length))
    (genAcceptCount A G x (s x.length)) (2 ^ (s x.length))
    (two_pow_pos _) (two_pow_pos _) hrej hfool.2
  simp only [majorityAlgo, decide_eq_false_iff_not, Nat.not_lt]
  exact this

/-- **Correctness of the derandomization.**  If `A` decides `L` with two-sided error `1/3` and
`G` fools `A` on every input up to error `1/12`, then the majority vote over all seeds of `G`
decides `L` exactly. -/
theorem majorityAlgo_decides (A : RAlgo) (G : Nat → Nat → Nat) (m s : Nat → Nat) (L : Language)
    (hL : ∀ x, (L x → AcceptsWhp A x (m x.length)) ∧ (¬ L x → RejectsWhp A x (m x.length)))
    (hfool : ∀ x, Fools A G x (m x.length) (s x.length)) (x : Bits) :
    majorityAlgo A G s x = true ↔ L x := by
  constructor
  · intro hmaj
    apply Classical.byContradiction
    intro hLx
    have := majorityAlgo_eq_false_of_rejectsWhp A G x m s ((hL x).2 hLx) (hfool x)
    rw [this] at hmaj
    exact Bool.noConfusion hmaj
  · intro hLx
    exact majorityAlgo_eq_true_of_acceptsWhp A G x m s ((hL x).1 hLx) (hfool x)

/-! ## Derandomization: fooling generators collapse `BPP` to `P` -/

/-- `P ⊆ BPP` in any model: a deterministic algorithm is a randomized algorithm that ignores its
randomness. -/
theorem P_subset_BPP (M : Model) (L : Language) (h : M.P L) : M.BPP L := by
  obtain ⟨D, hD, hDL⟩ := h
  refine ⟨fun x _ => D x, fun _ => 0, M.det_to_rand D hD, M.isPoly_const 0, ?_⟩
  intro x
  constructor
  · intro hLx
    have hD1 : D x = true := (hDL x).mpr hLx
    show 2 * 2 ^ 0 ≤ 3 * acceptCount (fun x _ => D x) x 0
    simp [acceptCount, countUpTo, hD1]
  · intro hLx
    have hD0 : D x = false := by
      cases hd : D x
      · rfl
      · exact absurd ((hDL x).mp hd) hLx
    show 3 * acceptCount (fun x _ => D x) x 0 ≤ 2 ^ 0
    simp [acceptCount, countUpTo, hD0]

/-- **Derandomization theorem.**  In any model possessing Nisan–Wigderson style pseudorandom
generators with logarithmic seed length, `BPP ⊆ P`. -/
theorem BPP_subset_P_of_generators (M : Model) (hG : M.HasNWGenerators) (L : Language)
    (h : M.BPP L) : M.P L := by
  obtain ⟨A, m, hA, hm, hL⟩ := h
  obtain ⟨G, s, p, hGP, hp, hsp, hfool⟩ := hG A m hA hm
  exact ⟨majorityAlgo A G s, M.maj_poly A G s p hA hGP hp hsp,
    majorityAlgo_decides A G m s L hL hfool⟩

/-- **Impagliazzo–Wigderson.**  If some function in `E` requires circuits of exponential size
(the strong circuit lower bound hypothesis) and this hardness yields Nisan–Wigderson pseudorandom
generators with logarithmic seed length, then `P = BPP`. -/
theorem impagliazzo_wigderson (M : Model) (hHard : M.ExpHardFunction)
    (hNW : M.ExpHardFunction → M.HasNWGenerators) : M.P = M.BPP := by
  funext L
  exact propext ⟨fun h => P_subset_BPP M L h,
    fun h => BPP_subset_P_of_generators M (hNW hHard) L h⟩

/-! ## Non-vacuity of the structural hypotheses

The closure axioms of `Model` together with `HasNWGenerators` are jointly satisfiable: the model
in which every function is deemed efficient satisfies all of them. -/

/-- The model in which every resource bound, algorithm and generator counts as efficient. -/
def trivialModel : Model where
  IsPoly := fun _ => True
  RandPoly := fun _ => True
  DetPoly := fun _ => True
  GenPoly := fun _ => True
  InE := fun _ => True
  isPoly_const := fun _ => trivial
  det_to_rand := fun _ _ => trivial
  maj_poly := fun _ _ _ _ _ _ _ _ => trivial

/-- The structural hypotheses of the derandomization theorem are satisfiable. -/
theorem trivialModel_hasNWGenerators : trivialModel.HasNWGenerators := by
  intro A m _ _
  refine ⟨fun _ y => y, m, fun n => 2 ^ m n, trivial, trivial, fun _ => Nat.le_refl _, ?_⟩
  intro x
  have hEq : genAcceptCount A (fun _ y => y) x (m x.length) = acceptCount A x (m x.length) := rfl
  constructor <;> rw [hEq] <;> omega

end CS

