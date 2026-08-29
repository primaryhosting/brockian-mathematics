import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace QI

/-- Bit strings of length `n`, as vectors over the field `ZMod 2`.
Addition is bitwise XOR. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟨x, y⟩ = ⨁ i, x i * y i`. -/
def ip {n : ℕ} (x y : BV n) : ZMod 2 := ∑ i, x i * y i

/-- `f` is an instance of Simon's problem with hidden shift `s`:
`f x = f y` exactly when `y = x` or `y = x ⊕ s`. -/
def IsSimon {n : ℕ} (s : BV n) (f : BV n → BV n) : Prop :=
  ∀ x y, f x = f y ↔ (y = x ∨ y = x + s)

/-! ## Basic arithmetic over `BV n` -/

theorem add_self_bv {n : ℕ} (x : BV n) : x + x = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  simpa using this (x i)

theorem add_add_cancel_bv {n : ℕ} (x s : BV n) : x + s + s = x := by
  funext i
  have : ∀ a b : ZMod 2, a + b + b = a := by decide
  simpa [add_assoc] using this (x i) (s i)

theorem ne_add_of_ne_zero {n : ℕ} (x : BV n) {s : BV n} (hs : s ≠ 0) : x ≠ x + s := by
  intro h
  apply hs
  funext i
  have h' : x i = x i + s i := congrFun h i
  have : ∀ a b : ZMod 2, a = a + b → b = 0 := by decide
  simpa using this (x i) (s i) h'

theorem ip_add_left {n : ℕ} (x y z : BV n) : ip (x + y) z = ip x z + ip y z := by
  simp [ip, add_mul, Finset.sum_add_distrib]

theorem ip_zero_left {n : ℕ} (y : BV n) : ip 0 y = 0 := by
  simp [ip]

/-! ## Quantum side: the interference pattern of a Simon query

After one query to `f` in superposition and a Hadamard transform, the (unnormalised)
amplitude of measuring the pair `(y, z)` is `∑_{x : f x = z} (-1)^{⟨x,y⟩}`. -/

/-- The sign character `χ : ZMod 2 → ℤ`, `χ a = (-1)^a`. -/
def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- The unnormalised amplitude of the outcome `(y, z)` in Simon's algorithm. -/
noncomputable def amp {n : ℕ} (f : BV n → BV n) (y z : BV n) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = z), chi (ip x y)

theorem fiber_eq_pair {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f) {x₀ z : BV n}
    (hx₀ : f x₀ = z) :
    Finset.univ.filter (fun x => f x = z) = ({x₀, x₀ + s} : Finset (BV n)) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hw
    have : f x₀ = f w := by rw [hx₀, hw]
    exact (hf x₀ w).1 this
  · intro hw
    have : f x₀ = f w := (hf x₀ w).2 hw
    rw [← this, hx₀]

/-- **Destructive interference.** Any outcome `y` that is *not* orthogonal to the hidden
shift `s` has zero amplitude: the quantum measurement always returns `y` with `⟨y,s⟩ = 0`. -/
theorem amp_eq_zero_of_ip_eq_one {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f)
    {y : BV n} (hy : ip s y = 1) (z : BV n) : amp f y z = 0 := by
  have hs : s ≠ 0 := by
    intro h
    rw [h, ip_zero_left] at hy
    exact absurd hy (by decide)
  by_cases hz : ∃ x₀, f x₀ = z
  · obtain ⟨x₀, hx₀⟩ := hz
    have hne : x₀ ≠ x₀ + s := ne_add_of_ne_zero x₀ hs
    rw [amp, fiber_eq_pair hf hx₀, Finset.sum_pair hne, ip_add_left, hy]
    have : ∀ a : ZMod 2, chi a + chi (a + 1) = 0 := by decide
    exact this _
  · push_neg at hz
    have : Finset.univ.filter (fun x => f x = z) = (∅ : Finset (BV n)) := by
      ext w; simp [hz w]
    rw [amp, this, Finset.sum_empty]

/-- **Constructive interference.** Every outcome `y` orthogonal to the hidden shift, paired
with a value `z` in the range of `f`, has nonzero amplitude, so the measurement outcomes are
exactly the vectors orthogonal to `s`. -/
theorem amp_ne_zero_of_ip_eq_zero {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f)
    (hs : s ≠ 0) {y : BV n} (hy : ip s y = 0) (x₀ : BV n) : amp f y (f x₀) ≠ 0 := by
  have hne : x₀ ≠ x₀ + s := ne_add_of_ne_zero x₀ hs
  rw [amp, fiber_eq_pair hf (rfl : f x₀ = f x₀), Finset.sum_pair hne, ip_add_left, hy]
  have : ∀ a : ZMod 2, chi a + chi (a + 0) ≠ 0 := by decide
  exact this _

/-- **`n` linear tests determine the hidden shift.** Hence the `O(n)` measurement outcomes
produced by the quantum algorithm suffice to identify `s`. -/
theorem shift_determined_by_orthogonality {n : ℕ} (s t : BV n)
    (h : ∀ i : Fin n, (ip (Pi.single i 1) s = 0 ↔ ip (Pi.single i 1) t = 0)) : s = t := by
  funext i
  have hs : ip (Pi.single i (1 : ZMod 2)) s = s i := by
    simp [ip, Pi.single_apply]
  have ht : ip (Pi.single i (1 : ZMod 2)) t = t i := by
    simp [ip, Pi.single_apply]
  have := h i
  rw [hs, ht] at this
  revert this
  have : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact this (s i) (t i)

/-! ## Classical side: deterministic adaptive query algorithms -/

/-- A deterministic adaptive decision tree making at most `q` queries to a function
`BV n → BV n` and returning an element of `BV n`. -/
inductive DTree (n : ℕ) : ℕ → Type
  | leaf {q : ℕ} (out : BV n) : DTree n q
  | node {q : ℕ} (x : BV n) (k : BV n → DTree n q) : DTree n (q + 1)

/-- The output of the algorithm on the oracle `f`. -/
def DTree.run {n : ℕ} : {q : ℕ} → DTree n q → (BV n → BV n) → BV n
  | _, .leaf o, _ => o
  | _, .node x k, f => (k (f x)).run f

/-- The set of points the algorithm queries when run on the oracle `f`. -/
def DTree.queries {n : ℕ} : {q : ℕ} → DTree n q → (BV n → BV n) → Finset (BV n)
  | _, .leaf _, _ => ∅
  | _, .node x k, f => insert x ((k (f x)).queries f)

theorem DTree.card_queries_le {n : ℕ} :
    ∀ {q : ℕ} (t : DTree n q) (f : BV n → BV n), (t.queries f).card ≤ q
  | _, .leaf _, _ => by simp [DTree.queries]
  | _, .node x k, f => by
      have h := DTree.card_queries_le (k (f x)) f
      have h2 := Finset.card_insert_le x ((k (f x)).queries f)
      simp only [DTree.queries]
      omega

theorem DTree.run_congr {n : ℕ} :
    ∀ {q : ℕ} (t : DTree n q) (f g : BV n → BV n),
      (∀ x ∈ t.queries f, g x = f x) → t.run g = t.run f
  | _, .leaf _, _, _, _ => rfl
  | _, .node x k, f, g, h => by
      have hx : g x = f x := h x (by simp [DTree.queries])
      have hrest : ∀ y ∈ (k (f x)).queries f, g y = f y := by
        intro y hy
        exact h y (by simp [DTree.queries, hy])
      simp only [DTree.run, hx]
      exact DTree.run_congr (k (f x)) f g hrest

/-! ## The adversary construction -/

/-- An arbitrary linear ordering of `BV n`, used to pick a canonical representative of
each coset `{x, x ⊕ s}`. -/
noncomputable def ordIdx (n : ℕ) : BV n ≃ Fin (Fintype.card (BV n)) := Fintype.equivFin _

/-- Given a set `Q` of already-queried points containing at most one element of each coset
of `{0, s}`, this is a Simon function with hidden shift `s` that acts as the identity on `Q`. -/
noncomputable def patch {n : ℕ} (Q : Finset (BV n)) (s : BV n) (x : BV n) : BV n :=
  if x ∈ Q then x
  else if x + s ∈ Q then x + s
  else if ordIdx n x ≤ ordIdx n (x + s) then x else x + s

theorem patch_mem {n : ℕ} {Q : Finset (BV n)} {s x : BV n} (hx : x ∈ Q) :
    patch Q s x = x := by
  simp [patch, hx]

theorem patch_spec {n : ℕ} (Q : Finset (BV n)) (s x : BV n) :
    patch Q s x = x ∨ patch Q s x = x + s := by
  unfold patch
  split_ifs <;> simp

theorem patch_shift {n : ℕ} {Q : Finset (BV n)} {s : BV n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) (x : BV n) :
    patch Q s (x + s) = patch Q s x := by
  have hcancel : x + s + s = x := add_add_cancel_bv x s
  by_cases h1 : x ∈ Q
  · have h2 : x + s ∉ Q := hQ x h1
    simp [patch, h1, h2, hcancel]
  · by_cases h2 : x + s ∈ Q
    · simp [patch, h1, h2]
    · have hne : x ≠ x + s := ne_add_of_ne_zero x hs
      have hene : ordIdx n x ≠ ordIdx n (x + s) := fun h => hne ((ordIdx n).injective h)
      by_cases h3 : ordIdx n x ≤ ordIdx n (x + s)
      · have h4 : ¬ (ordIdx n (x + s) ≤ ordIdx n x) := by
          intro h; exact hene (le_antisymm h3 h)
        simp [patch, h1, h2, h3, h4, hcancel]
      · have h4 : ordIdx n (x + s) ≤ ordIdx n x := le_of_not_ge h3
        simp [patch, h1, h2, h3, h4, hcancel]

theorem isSimon_patch {n : ℕ} {Q : Finset (BV n)} {s : BV n} (hs : s ≠ 0)
    (hQ : ∀ x ∈ Q, x + s ∉ Q) : IsSimon s (patch Q s) := by
  intro x y
  constructor
  · intro h
    rcases patch_spec Q s x with hx | hx <;> rcases patch_spec Q s y with hy | hy
    · left; rw [← hx, ← hy, h]
    · right
      have : x = y + s := by rw [← hx, ← hy, h]
      rw [this, add_add_cancel_bv]
    · right
      have : x + s = y := by rw [← hx, ← hy, h]
      exact this.symm
    · left
      have : x + s = y + s := by rw [← hx, ← hy, h]
      have := congrArg (fun z => z + s) this
      simpa [add_add_cancel_bv] using this.symm
  · intro h
    rcases h with h | h
    · rw [h]
    · rw [h, patch_shift hs hQ]

/-- Simon instances exist for every nonzero hidden shift, so the statements above are not
vacuous. -/
theorem exists_isSimon {n : ℕ} {s : BV n} (hs : s ≠ 0) : ∃ f : BV n → BV n, IsSimon s f :=
  ⟨patch ∅ s, isSimon_patch hs (by simp)⟩

/-- **Classical lower bound.** Any deterministic adaptive algorithm making at most `q`
queries that always outputs the hidden shift must satisfy `2^n ≤ q^2 + 2`. -/
theorem classical_query_lower_bound {n q : ℕ} (t : DTree n q)
    (hcorrect : ∀ s : BV n, s ≠ 0 → ∀ f, IsSimon s f → t.run f = s) :
    2 ^ n ≤ q * q + 2 := by
  by_contra hcon
  push_neg at hcon
  set Q : Finset (BV n) := t.queries id with hQdef
  set o : BV n := t.run id with hodef
  set D : Finset (BV n) :=
    ((Q ×ˢ Q).image (fun p => p.1 + p.2)) ∪ {0, o} with hDdef
  have hQcard : Q.card ≤ q := DTree.card_queries_le t id
  have hDcard : D.card ≤ q * q + 2 := by
    have h1 : ((Q ×ˢ Q).image (fun p => p.1 + p.2)).card ≤ q * q := by
      refine le_trans (Finset.card_image_le) ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hQcard hQcard
    have h2 : ({0, o} : Finset (BV n)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hcardV : Fintype.card (BV n) = 2 ^ n := by simp
  have hex : ∃ s : BV n, s ∉ D := by
    by_contra hall
    push_neg at hall
    have : (Finset.univ : Finset (BV n)) ⊆ D := fun x _ => hall x
    have := Finset.card_le_card this
    rw [Finset.card_univ, hcardV] at this
    omega
  obtain ⟨s, hsD⟩ := hex
  have hs0 : s ≠ 0 := by
    intro h; exact hsD (by simp [hDdef, h])
  have hso : s ≠ o := by
    intro h; exact hsD (by simp [hDdef, h])
  have hQs : ∀ x ∈ Q, x + s ∉ Q := by
    intro x hx hxs
    refine hsD ?_
    simp only [hDdef, Finset.mem_union, Finset.mem_image, Finset.mem_product]
    left
    exact ⟨(x, x + s), by simp [hx, hxs], by
      rw [← add_assoc, add_self_bv, zero_add]⟩
  have hsim : IsSimon s (patch Q s) := isSimon_patch hs0 hQs
  have hagree : ∀ x ∈ t.queries id, patch Q s x = id x := by
    intro x hx
    exact patch_mem hx
  have hrun : t.run (patch Q s) = o := DTree.run_congr t id (patch Q s) hagree
  have := hcorrect s hs0 (patch Q s) hsim
  rw [hrun] at this
  exact hso this.symm

/-- **`Ω(2^{n/2})` classical queries.** -/
theorem classical_query_lower_bound_exp {n q : ℕ} (hn : 2 ≤ n) (t : DTree n q)
    (hcorrect : ∀ s : BV n, s ≠ 0 → ∀ f, IsSimon s f → t.run f = s) :
    2 ^ ((n - 1) / 2) ≤ q := by
  have h := classical_query_lower_bound t hcorrect
  have h1 : 2 ^ (n - 1) ≤ q * q := by
    have h2 : (2:ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (2:ℕ) ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 2 ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) ≤ 2 ^ (n - 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.mul_self_le_mul_self_iff.mp (le_trans h4 h1)

/-- **Simon's problem.**

* (quantum, part 1) every measurement outcome of the quantum algorithm is orthogonal to the
  hidden shift `s` (outcomes `y` with `⟨s,y⟩ = 1` have amplitude `0`);
* (quantum, part 2) all outcomes orthogonal to `s` do occur (nonzero amplitude);
* (quantum, part 3) `n` such linear constraints determine `s`, so `O(n)` quantum queries suffice;
* (classical) every deterministic adaptive classical algorithm that always outputs the hidden
  shift needs `q` queries with `2^n ≤ q^2 + 2`, hence `q ≥ 2^{(n-1)/2} = Ω(2^{n/2})`.
-/
theorem simon_algorithm :
    (∀ (n : ℕ) (s y z : BV n) (f : BV n → BV n), IsSimon s f → ip s y = 1 → amp f y z = 0) ∧
    (∀ (n : ℕ) (s y x₀ : BV n) (f : BV n → BV n), IsSimon s f → s ≠ 0 → ip s y = 0 →
      amp f y (f x₀) ≠ 0) ∧
    (∀ (n : ℕ) (s t : BV n),
      (∀ i : Fin n, (ip (Pi.single i 1) s = 0 ↔ ip (Pi.single i 1) t = 0)) → s = t) ∧
    (∀ (n q : ℕ) (t : DTree n q),
      (∀ s : BV n, s ≠ 0 → ∀ f, IsSimon s f → t.run f = s) → 2 ^ n ≤ q * q + 2) ∧
    (∀ (n q : ℕ), 2 ≤ n → ∀ t : DTree n q,
      (∀ s : BV n, s ≠ 0 → ∀ f, IsSimon s f → t.run f = s) → 2 ^ ((n - 1) / 2) ≤ q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n s y z f hf hy
    exact amp_eq_zero_of_ip_eq_one hf hy z
  · intro n s y x₀ f hf hs hy
    exact amp_ne_zero_of_ip_eq_zero hf hs hy x₀
  · intro n s t h
    exact shift_determined_by_orthogonality s t h
  · intro n q t h
    exact classical_query_lower_bound t h
  · intro n q hn t h
    exact classical_query_lower_bound_exp hn t h

end QI

