/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/
def Gate.eval (env : List Bool) : Gate → Bool
  | .const b => b
  | .not a => !(env.getD a false)
  | .and a b => (env.getD a false) && (env.getD b false)
  | .or a b => (env.getD a false) || (env.getD b false)

/-- Running a straight-line program: each gate appends its value to the environment. -/
def evalAux : List Bool → Circuit → List Bool
  | env, [] => env
  | env, g :: C => evalAux (env ++ [g.eval env]) C

/-- The value computed by a circuit on an input: the value of its last gate. -/
def Circuit.eval (C : Circuit) (x : List Bool) : Bool :=
  ((evalAux x C).getLast?).getD false

/-- The size of a circuit is its number of gates. -/
def Circuit.size (C : Circuit) : ℕ := C.length

/-! ## Exponential circuit hardness -/

/-- `ExpCircuitHard L` says that the Boolean function `L` has circuit complexity `2^(Ω(n))`:
there is `k > 0` such that for every input length `n`, no circuit of size `< 2 ^ (n / k)`
agrees with `L` on all inputs of length `n`.  This is the "strong circuit lower bound"
hypothesis of Impagliazzo–Wigderson. -/
def ExpCircuitHard (L : List Bool → Bool) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, ∀ C : Circuit, C.size < 2 ^ (n / k) →
    ∃ x : List Bool, x.length = n ∧ C.eval x ≠ L x

/-! ### Clamping gate indices -/

def Gate.clampIdx (N i : ℕ) : ℕ := if i < N then i else N - 1

def Gate.clamp (N : ℕ) : Gate → Gate
  | .const b => .const b
  | .not a => .not (Gate.clampIdx N a)
  | .and a b => .and (Gate.clampIdx N a) (Gate.clampIdx N b)
  | .or a b => .or (Gate.clampIdx N a) (Gate.clampIdx N b)

lemma getD_clampIdx {env : List Bool} {N : ℕ} (h : env.length < N) (i : ℕ) :
    env[Gate.clampIdx N i]?.getD false = env[i]?.getD false := by
  unfold Gate.clampIdx
  by_cases hi : i < N
  · simp [hi]
  · have h1 : env[i]? = none := List.getElem?_eq_none (by omega)
    have h2 : env[N - 1]? = none := List.getElem?_eq_none (by omega)
    simp [hi, h1, h2]

lemma Gate.eval_clamp {env : List Bool} {N : ℕ} (h : env.length < N) (g : Gate) :
    (g.clamp N).eval env = g.eval env := by
  cases g <;> simp [Gate.clamp, Gate.eval, getD_clampIdx h]

lemma evalAux_clamp (N : ℕ) : ∀ (C : Circuit) (env : List Bool),
    env.length + C.length ≤ N → evalAux env (C.map (Gate.clamp N)) = evalAux env C := by
  intro C
  induction C with
  | nil => intro env _; simp [evalAux]
  | cons g C ih =>
    intro env h
    simp only [List.map_cons, evalAux, List.length_cons] at *
    rw [Gate.eval_clamp (by omega) g]
    exact ih _ (by simp; omega)

lemma Circuit.eval_clamp {N : ℕ} (C : Circuit) (x : List Bool)
    (h : x.length + C.length ≤ N) : Circuit.eval (C.map (Gate.clamp N)) x = C.eval x := by
  unfold Circuit.eval
  rw [evalAux_clamp N C x h]


/-! ### Counting circuits (Shannon's bound) -/

/-- The (finite) set of gates all of whose indices are `< N`. -/
def gateSet (N : ℕ) : Finset Gate :=
  ({Gate.const false, Gate.const true} : Finset Gate)
    ∪ (Finset.range N).image Gate.not
    ∪ ((Finset.range N) ×ˢ (Finset.range N)).image (fun p => Gate.and p.1 p.2)
    ∪ ((Finset.range N) ×ˢ (Finset.range N)).image (fun p => Gate.or p.1 p.2)

lemma const_false_mem_gateSet (N : ℕ) : Gate.const false ∈ gateSet N := by
  simp [gateSet]

lemma clamp_mem_gateSet {N : ℕ} (hN : 0 < N) (g : Gate) : g.clamp N ∈ gateSet N := by
  have hclamp : ∀ i : ℕ, Gate.clampIdx N i < N := by
    intro i; unfold Gate.clampIdx; split <;> omega
  cases g with
  | const b => cases b <;> simp [gateSet, Gate.clamp]
  | not a =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    exact Or.inl (Or.inl (Or.inr ⟨_, hclamp a, rfl⟩))
  | and a b =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_range]
    exact Or.inl (Or.inr ⟨(_, _), ⟨hclamp a, hclamp b⟩, rfl⟩)
  | or a b =>
    simp only [Gate.clamp, gateSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_range]
    exact Or.inr ⟨(_, _), ⟨hclamp a, hclamp b⟩, rfl⟩

lemma card_gateSet_le (N : ℕ) : (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := by
  have h1 : (({Gate.const false, Gate.const true} : Finset Gate)).card ≤ 2 :=
    Finset.card_insert_le _ _ |>.trans (by simp)
  have h2 : ((Finset.range N).image Gate.not).card ≤ N := by
    simpa using Finset.card_image_le (s := Finset.range N) (f := Gate.not)
  have h3 : (((Finset.range N) ×ˢ (Finset.range N)).image
      (fun p : ℕ × ℕ => Gate.and p.1 p.2)).card ≤ N ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    simp [Finset.card_product, sq]
  have h4 : (((Finset.range N) ×ˢ (Finset.range N)).image
      (fun p : ℕ × ℕ => Gate.or p.1 p.2)).card ≤ N ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    simp [Finset.card_product, sq]
  have := Finset.card_union_le
    (((({Gate.const false, Gate.const true} : Finset Gate)
      ∪ (Finset.range N).image Gate.not)
      ∪ ((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.and p.1 p.2)))
    (((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.or p.1 p.2))
  have h5 := Finset.card_union_le
    ((({Gate.const false, Gate.const true} : Finset Gate)
      ∪ (Finset.range N).image Gate.not))
    (((Finset.range N) ×ˢ (Finset.range N)).image (fun p : ℕ × ℕ => Gate.and p.1 p.2))
  have h6 := Finset.card_union_le
    (({Gate.const false, Gate.const true} : Finset Gate))
    ((Finset.range N).image Gate.not)
  unfold gateSet
  omega

/-- **Shannon's counting bound.**  If there are fewer circuit codes of size `s` than Boolean
functions on `n` bits, then some Boolean function on `n` bits is not computed by any circuit
of size at most `s`. -/
lemma exists_hard_function (n s : ℕ)
    (h : (gateSet (n + s)).card ^ s * (s + 1) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuit, C.length ≤ s →
      ∃ y : Fin n → Bool, C.eval (List.ofFn y) ≠ f y := by
  set N := n + s with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- degenerate case: no inputs and no gates
    have hn : n = 0 := by omega
    have hs : s = 0 := by omega
    subst hn; subst hs
    refine ⟨fun _ => true, ?_⟩
    intro C hC
    have : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨fun i => i.elim0, by simp [Circuit.eval, evalAux]⟩
  · classical
    set G := {g : Gate // g ∈ gateSet N}
    set Φ : ((Fin s → G) × Fin (s + 1)) → ((Fin n → Bool) → Bool) :=
      fun t y => Circuit.eval ((List.ofFn (fun i => (t.1 i : Gate))).take (t.2 : ℕ))
        (List.ofFn y) with hΦ
    have hcardT : Fintype.card ((Fin s → G) × Fin (s + 1))
        = (gateSet N).card ^ s * (s + 1) := by
      simp [Fintype.card_prod, G]
    have hcardB : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
      simp
    have hnotsurj : ¬ Function.Surjective Φ := by
      intro hsurj
      have := Fintype.card_le_of_surjective Φ hsurj
      rw [hcardT, hcardB] at this
      omega
    simp only [Function.Surjective, not_forall] at hnotsurj
    obtain ⟨f, hf⟩ := hnotsurj
    refine ⟨f, ?_⟩
    intro C hC
    by_contra hcon
    push_neg at hcon
    -- the clamped circuit
    set C' := C.map (Gate.clamp N) with hC'
    have hlen : C'.length = C.length := by simp [hC']
    have hmem : ∀ i, ∀ hi : i < C'.length, C'[i] ∈ gateSet N := by
      intro i hi
      have hi' : i < C.length := by simpa [hC'] using hi
      have heq : C'[i] = Gate.clamp N (C[i]'hi') := by simp [hC']
      rw [heq]
      exact clamp_mem_gateSet hNpos _
    set g : Fin s → G := fun i =>
      if hi : (i : ℕ) < C'.length then ⟨C'[(i : ℕ)], hmem _ hi⟩
      else ⟨Gate.const false, const_false_mem_gateSet N⟩ with hg
    have hlen' : C'.length ≤ s := by omega
    have htake : (List.ofFn (fun i => (g i : Gate))).take C'.length = C' := by
      apply List.ext_getElem
      · simp [hlen']
      · intro i h1 h2
        have hi : i < C'.length := by simpa [hlen'] using h1
        simp [List.getElem_take, hg, hi]
    have hΦt : Φ (g, ⟨C'.length, by omega⟩) = f := by
      funext y
      rw [hΦ]
      simp only [htake]
      have hev : Circuit.eval C' (List.ofFn y) = C.eval (List.ofFn y) :=
        Circuit.eval_clamp C (List.ofFn y) (by simp [hN]; omega)
      rw [hev, hcon y]
    exact hf ⟨_, hΦt⟩

/-! ### Existence of exponentially hard Boolean functions -/

/-- A list-valued version of Shannon's counting bound. -/
lemma exists_hard_function_list (n s : ℕ)
    (h : (gateSet (n + s)).card ^ s * (s + 1) < 2 ^ 2 ^ n) :
    ∃ f : List Bool → Bool, ∀ C : Circuit, C.length ≤ s →
      ∃ x : List Bool, x.length = n ∧ C.eval x ≠ f x := by
  obtain ⟨f₀, hf₀⟩ := exists_hard_function n s h
  classical
  refine ⟨fun x => if hx : x.length = n then f₀ (fun i => x.get (Fin.cast hx.symm i)) else false,
    ?_⟩
  intro C hC
  obtain ⟨y, hy⟩ := hf₀ C hC
  refine ⟨List.ofFn y, by simp, ?_⟩
  have hx : (List.ofFn y).length = n := by simp
  simp only [hx, dif_pos]
  have : (fun i => (List.ofFn y).get (Fin.cast hx.symm i)) = y := by
    funext i
    simp
  rw [this]
  exact hy

lemma lin_le_two_pow {q : ℕ} (h : 25 ≤ q) : 8 * q + 11 ≤ 2 ^ q := by
  induction q, h using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have h2 : (8 : ℕ) ≤ 2 ^ q := le_trans (by omega) ih
    have : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by ring
    omega

lemma two_n_le_two_pow {n : ℕ} (h : 100 ≤ n) : 2 * n + 5 ≤ 2 ^ (n / 4) := by
  have hq : 25 ≤ n / 4 := by omega
  have := lin_le_two_pow hq
  have hn : n ≤ 4 * (n / 4) + 3 := by omega
  omega

/-- The counting bound is satisfied for circuits of size below `2 ^ (n / 100)`. -/
lemma shannon_bound (n : ℕ) :
    (gateSet (n + (2 ^ (n / 100) - 1))).card ^ (2 ^ (n / 100) - 1) * (2 ^ (n / 100) - 1 + 1)
      < 2 ^ 2 ^ n := by
  set t := n / 100 with ht
  set s := 2 ^ t - 1 with hs
  set N := n + s with hN
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hs1 : s + 1 = 2 ^ t := by omega
  rcases lt_or_ge n 100 with hn | hn
  · -- then `t = 0` and there is a single circuit code
    have ht0 : t = 0 := by omega
    have hs0 : s = 0 := by simp [hs, ht0]
    have h2 : 2 ≤ 2 ^ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    simp only [hs0, pow_zero, one_mul]
    omega
  · -- the main case
    have hbase : (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := card_gateSet_le N
    have hpoly := two_n_le_two_pow hn
    have hts : t ≤ n / 4 := by omega
    have hsle : s ≤ 2 ^ (n / 4) := by
      have : 2 ^ t ≤ 2 ^ (n / 4) := Nat.pow_le_pow_right (by norm_num) hts
      omega
    have hnle : n ≤ 2 ^ (n / 4) := by omega
    have hNle : N ≤ 2 ^ (n / 4 + 1) := by
      have : 2 ^ (n / 4 + 1) = 2 ^ (n / 4) + 2 ^ (n / 4) := by ring
      omega
    have hN1 : 1 ≤ N := by omega
    -- bound the number of gates by a power of two
    have hgate : (gateSet N).card ≤ 2 ^ (2 * (n / 4) + 5) := by
      have h5 : 2 + N + 2 * N ^ 2 ≤ 8 * N ^ 2 := by nlinarith
      have h6 : N ^ 2 ≤ (2 ^ (n / 4 + 1)) ^ 2 := Nat.pow_le_pow_left hNle 2
      have h7 : (8 : ℕ) * (2 ^ (n / 4 + 1)) ^ 2 = 2 ^ (2 * (n / 4) + 5) := by
        rw [← pow_mul]
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        ring_nf
      calc (gateSet N).card ≤ 2 + N + 2 * N ^ 2 := hbase
        _ ≤ 8 * N ^ 2 := h5
        _ ≤ 8 * (2 ^ (n / 4 + 1)) ^ 2 := by exact Nat.mul_le_mul_left 8 h6
        _ = 2 ^ (2 * (n / 4) + 5) := h7
    -- the exponent of the total count is small
    have hexp : (2 * (n / 4) + 5) * s + t < 2 ^ n := by
      have h1 : 2 * (n / 4) + 5 ≤ 2 ^ (n / 4) := by omega
      have h2 : (2 * (n / 4) + 5) * s ≤ 2 ^ (n / 4) * 2 ^ (n / 4) :=
        Nat.mul_le_mul h1 hsle
      have h3 : 2 ^ (n / 4) * 2 ^ (n / 4) = 2 ^ (2 * (n / 4)) := by
        rw [← pow_add]; ring_nf
      have h4 : t ≤ 2 ^ (n / 4) := le_trans (by omega) hnle
      have h5 : 2 ^ (n / 4) ≤ 2 ^ (2 * (n / 4)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : 2 ^ (2 * (n / 4)) + 2 ^ (2 * (n / 4)) = 2 ^ (2 * (n / 4) + 1) := by ring
      have h7 : 2 ^ (2 * (n / 4) + 1) ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h8 : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    calc (gateSet N).card ^ s * (s + 1)
        ≤ (2 ^ (2 * (n / 4) + 5)) ^ s * 2 ^ t := by
          rw [hs1]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hgate s)
      _ = 2 ^ ((2 * (n / 4) + 5) * s + t) := by rw [← pow_mul, ← pow_add]
      _ < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hexp

/-- **Shannon's theorem.**  There exist Boolean functions of exponential circuit complexity. -/
theorem exists_expCircuitHard : ∃ L : List Bool → Bool, ExpCircuitHard L := by
  choose F hF using fun n : ℕ =>
    exists_hard_function_list n (2 ^ (n / 100) - 1) (shannon_bound n)
  refine ⟨fun x => F x.length x, 100, by norm_num, ?_⟩
  intro n C hC
  have hCle : C.length ≤ 2 ^ (n / 100) - 1 := by
    have : C.length < 2 ^ (n / 100) := hC
    omega
  obtain ⟨x, hx, hne⟩ := hF n C hCle
  exact ⟨x, hx, by show C.eval x ≠ F x.length x; rwa [hx]⟩



/-! ## An abstract model of uniform computation -/

/-- An abstract model of uniform (deterministic) computation.  It provides the classes of
polynomial-time computable predicates and functions of one and of two string arguments,
together with the class `InE` of functions computable in time `2 ^ (O(n))`, and the three
closure properties of any reasonable machine model that we need:

* a polynomial-time predicate is a polynomial-time predicate of an extra dummy argument;
* polynomial-time predicates are closed under substitution of polynomial-time functions;
* the *majority over all strings of logarithmic length* of a polynomial-time predicate is
  again polynomial time (exhaustive search over `2 ^ O(log n) = poly(n)` many strings). -/
structure Model where
  /-- Polynomial-time decidable predicates of one string. -/
  PolyP : (List Bool → Bool) → Prop
  /-- Polynomial-time decidable predicates of two strings. -/
  PolyP2 : (List Bool → List Bool → Bool) → Prop
  /-- Polynomial-time computable functions of one string. -/
  PolyF : (List Bool → List Bool) → Prop
  /-- Polynomial-time computable functions of two strings. -/
  PolyF2 : (List Bool → List Bool → List Bool) → Prop
  /-- Predicates computable in deterministic time `2 ^ (O(n))` (the class `E`). -/
  InE : (List Bool → Bool) → Prop
  /-- Adding a dummy second argument keeps a predicate polynomial time. -/
  polyP2_of_polyP : ∀ f : List Bool → Bool, PolyP f → PolyP2 (fun x _ => f x)
  /-- Substituting a polynomial-time function into a polynomial-time predicate. -/
  polyP2_subst : ∀ (A : List Bool → List Bool → Bool) (G : List Bool → List Bool → List Bool),
    PolyP2 A → PolyF2 G → PolyP2 (fun x y => A x (G x y))
  /-- Exhaustive search over all strings of logarithmic length is polynomial time. -/
  polyP_majority_log : ∀ (f : List Bool → List Bool → Bool) (s : ℕ → ℕ),
    PolyP2 f → PolyF (fun x => List.replicate (s x.length) false) →
    (∃ c : ℕ, ∀ n : ℕ, s n ≤ c * (Nat.log 2 (n + 1) + 1)) →
    PolyP (fun x => decide (2 ^ (s x.length) <
      2 * (Finset.univ.filter
        (fun y : Fin (s x.length) → Bool => f x (List.ofFn y) = true)).card))

/-! ## Probabilities -/

/-- The fraction of strings `y ∈ {0,1}^k` on which `f` returns `true`. -/
def avgTrue (k : ℕ) (f : (Fin k → Bool) → Bool) : ℚ :=
  ((Finset.univ.filter (fun y : Fin k → Bool => f y = true)).card : ℚ) / 2 ^ k

/-- If the acceptance fraction exceeds `1/2`, the majority vote accepts. -/
lemma card_gt_of_avgTrue_gt_half {k : ℕ} {f : (Fin k → Bool) → Bool}
    (h : (1 : ℚ) / 2 < avgTrue k f) :
    2 ^ k < 2 * (Finset.univ.filter (fun y : Fin k → Bool => f y = true)).card := by
  set c : ℕ := (Finset.univ.filter (fun y : Fin k → Bool => f y = true)).card with hc
  have hpos : (0 : ℚ) < 2 ^ k := by positivity
  rw [avgTrue, ← hc, lt_div_iff₀ hpos] at h
  have : ((2 ^ k : ℕ) : ℚ) < ((2 * c : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast this

/-- If the acceptance fraction is below `1/2`, the majority vote rejects. -/
lemma card_le_of_avgTrue_lt_half {k : ℕ} {f : (Fin k → Bool) → Bool}
    (h : avgTrue k f < (1 : ℚ) / 2) :
    ¬ 2 ^ k < 2 * (Finset.univ.filter (fun y : Fin k → Bool => f y = true)).card := by
  set c : ℕ := (Finset.univ.filter (fun y : Fin k → Bool => f y = true)).card with hc
  have hpos : (0 : ℚ) < 2 ^ k := by positivity
  rw [avgTrue, ← hc, div_lt_iff₀ hpos] at h
  have : ((2 * c : ℕ) : ℚ) < ((2 ^ k : ℕ) : ℚ) := by push_cast; linarith
  have : 2 * c < 2 ^ k := by exact_mod_cast this
  omega

/-! ## The classes P and BPP -/

/-- Polynomially bounded functions. -/
def PolyBound (m : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n : ℕ, m n ≤ c * n ^ d + c

/-- The class `P` of the model. -/
def Model.P (M : Model) (L : List Bool → Bool) : Prop := M.PolyP L

/-- The class `BPP`: a polynomial-time predicate `A` of the input and of a polynomially long
random string decides `L` with error probability at most `1/3`. -/
def Model.BPP (M : Model) (L : List Bool → Bool) : Prop :=
  ∃ (A : List Bool → List Bool → Bool) (m : ℕ → ℕ),
    M.PolyP2 A ∧ PolyBound m ∧
    ∀ x : List Bool,
      (L x = true → (2 : ℚ) / 3 ≤ avgTrue (m x.length) (fun r => A x (List.ofFn r))) ∧
      (L x = false → avgTrue (m x.length) (fun r => A x (List.ofFn r)) ≤ (1 : ℚ) / 3)

/-! ## Quick pseudorandom generators and derandomization -/

/-- A *quick* pseudorandom generator for `m`-bit tests: it is computable in polynomial time,
uses only `O(log n)` random bits of seed, and its output fools every polynomial-time test
(on every fixed input `x`, which is where non-uniformity of the test would enter) with
error at most `1/12`. -/
structure PRG (M : Model) (m : ℕ → ℕ) where
  /-- The generator: on input `x` and seed `y` it outputs a pseudorandom string. -/
  G : List Bool → List Bool → List Bool
  /-- The seed length as a function of the input length. -/
  s : ℕ → ℕ
  /-- The generator is polynomial-time computable. -/
  polyG : M.PolyF2 G
  /-- The seed length is polynomial-time computable (in unary). -/
  polyS : M.PolyF (fun x => List.replicate (s x.length) false)
  /-- The seed length is logarithmic. -/
  logSeed : ∃ c : ℕ, ∀ n : ℕ, s n ≤ c * (Nat.log 2 (n + 1) + 1)
  /-- The generator fools all polynomial-time tests on every input. -/
  fools : ∀ A : List Bool → List Bool → Bool, M.PolyP2 A → ∀ x : List Bool,
    |avgTrue (m x.length) (fun r => A x (List.ofFn r))
      - avgTrue (s x.length) (fun y => A x (G x (List.ofFn y)))| ≤ (1 : ℚ) / 12

/-- The derandomization hypothesis: quick pseudorandom generators exist for every
polynomial output length.  This is the conclusion of the Nisan–Wigderson construction
combined with hardness amplification. -/
def DerandomizationHypothesis (M : Model) : Prop :=
  ∀ m : ℕ → ℕ, PolyBound m → Nonempty (PRG M m)

/-- **Derandomization.**  If quick pseudorandom generators exist, then every `BPP` language
is in `P`: replace the random string by the output of the generator and take the majority
vote over the (polynomially many) seeds. -/
theorem bpp_subset_p_of_prg (M : Model) (hPRG : DerandomizationHypothesis M)
    (L : List Bool → Bool) (hL : M.BPP L) : M.P L := by
  obtain ⟨A, m, hA, hm, hcorrect⟩ := hL
  obtain ⟨g⟩ := hPRG m hm
  -- the derandomized test
  have hf : M.PolyP2 (fun x y => A x (g.G x y)) := M.polyP2_subst A g.G hA g.polyG
  have hD := M.polyP_majority_log (fun x y => A x (g.G x y)) g.s hf g.polyS g.logSeed
  -- the majority vote computes `L`
  have hEq : (fun x : List Bool => decide (2 ^ (g.s x.length) <
      2 * (Finset.univ.filter
        (fun y : Fin (g.s x.length) → Bool => A x (g.G x (List.ofFn y)) = true)).card)) = L := by
    funext x
    have hfool := g.fools A hA x
    rcases hLx : L x with _ | _
    · have h13 := (hcorrect x).2 hLx
      have hhalf : avgTrue (g.s x.length) (fun y => A x (g.G x (List.ofFn y))) < (1 : ℚ) / 2 := by
        have := abs_le.mp hfool
        linarith [this.1, this.2]
      simpa using card_le_of_avgTrue_lt_half hhalf
    · have h23 := (hcorrect x).1 hLx
      have hhalf : (1 : ℚ) / 2 < avgTrue (g.s x.length) (fun y => A x (g.G x (List.ofFn y))) := by
        have := abs_le.mp hfool
        linarith [this.1, this.2]
      simpa using card_gt_of_avgTrue_gt_half hhalf
  rw [hEq] at hD
  exact hD

/-- Every language in `P` is in `BPP` (run the deterministic algorithm, ignoring randomness). -/
theorem p_subset_bpp (M : Model) (L : List Bool → Bool) (hL : M.P L) : M.BPP L := by
  refine ⟨fun x _ => L x, fun _ => 0, M.polyP2_of_polyP L hL, ⟨0, 0, by simp⟩, ?_⟩
  intro x
  constructor
  · intro h
    have : avgTrue 0 (fun _ : Fin 0 → Bool => L x) = 1 := by
      simp [avgTrue, h, Finset.filter_true_of_mem]
    rw [this]; norm_num
  · intro h
    have : avgTrue 0 (fun _ : Fin 0 → Bool => L x) = 0 := by
      simp [avgTrue, h]
    rw [this]; norm_num

/-! ## The Impagliazzo–Wigderson theorem -/

/-- The strong circuit lower bound hypothesis of Impagliazzo–Wigderson: some language in `E`
requires circuits of size `2 ^ (Ω(n))`. -/
def HardnessHypothesis (M : Model) : Prop :=
  ∃ L : List Bool → Bool, M.InE L ∧ ExpCircuitHard L

/-- **Impagliazzo–Wigderson.**  Strong circuit lower bounds imply `P = BPP`.

The hypothesis `hNW` is the hardness-versus-randomness construction: from a language in `E`
of exponential circuit complexity one obtains quick pseudorandom generators (Nisan–Wigderson
generator together with hardness amplification); it is taken here as an assumption.  What is
proved here is the derandomization half of the argument in full: given the generators, the
majority vote over all seeds turns any bounded-error probabilistic polynomial-time algorithm
into an equivalent deterministic polynomial-time one, so that `BPP = P`; the converse
inclusion `P ⊆ BPP` is proved as well. -/
theorem impagliazzo_wigderson (M : Model)
    (hNW : HardnessHypothesis M → DerandomizationHypothesis M)
    (hHard : HardnessHypothesis M) :
    ∀ L : List Bool → Bool, M.BPP L ↔ M.P L :=
  fun L => ⟨bpp_subset_p_of_prg M (hNW hHard) L, p_subset_bpp M L⟩

/-! ## Consistency of the hypotheses

The hypotheses of `CS.impagliazzo_wigderson` are satisfiable: we exhibit a (degenerate)
computation model in which they all hold.  Together with Shannon's theorem
`CS.exists_expCircuitHard`, which shows that exponentially circuit-hard Boolean functions do
exist, this rules out the statement being vacuous. -/

/-- A degenerate computation model in which no predicate is polynomial time.  It satisfies all
the closure axioms of `CS.Model` and, vacuously, the derandomization hypothesis. -/
def emptyModel : Model where
  PolyP := fun _ => False
  PolyP2 := fun _ => False
  PolyF := fun _ => True
  PolyF2 := fun _ => True
  InE := fun _ => True
  polyP2_of_polyP := fun _ h => h
  polyP2_subst := fun _ _ h _ => h
  polyP_majority_log := fun _ _ h _ _ => h

theorem hypotheses_satisfiable :
    ∃ M : Model, HardnessHypothesis M ∧ DerandomizationHypothesis M := by
  refine ⟨emptyModel, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := exists_expCircuitHard
    exact ⟨L, trivial, hL⟩
  · intro m _
    exact ⟨{ G := fun _ _ => []
             s := fun _ => 0
             polyG := trivial
             polyS := trivial
             logSeed := ⟨0, fun _ => by simp⟩
             fools := fun _ h _ => absurd h (fun h => h) }⟩


end CS

