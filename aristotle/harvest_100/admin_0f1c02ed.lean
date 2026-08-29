import RequestProject.TodaCube

/-!
# Affine hashing over GF(2) and the isolation lemma

We encode an affine hash function `y ↦ A y + b` from `GF(2)^q` to `GF(2)^k` as a bit string
consisting of `q+4` blocks of length `q+1`; block `i` consists of the `i`-th row of `A`
followed by the `i`-th coordinate of `b`.  Only the first `k` blocks are used.

The main results are the two counting lemmas (uniformity and pairwise independence) and the
Valiant–Vazirani isolation lemma `CS.isolation`.
-/

open Classical BigOperators

namespace CS

/-- Inner product over `GF(2)` of two bit strings. -/
def dot : Str → Str → Bool
  | [], _ => false
  | _, [] => false
  | (a :: as), (y :: ys) => xor (a && y) (dot as ys)

@[simp] lemma dot_nil_left (y : Str) : dot [] y = false := by cases y <;> rfl
@[simp] lemma dot_nil_right (a : Str) : dot a [] = false := by cases a <;> rfl
@[simp] lemma dot_cons (a : Bool) (as : Str) (y : Bool) (ys : Str) :
    dot (a :: as) (y :: ys) = xor (a && y) (dot as ys) := rfl

/-- The number of bits used to describe one hash function on `q`-bit inputs. -/
def hashLen (q : ℕ) : ℕ := (q + 4) * (q + 1)

/-- `Hit q k h y` says that the affine map described by `h`, truncated to its first `k`
output coordinates, maps `y` to `0`. -/
def Hit (q k : ℕ) (h y : Str) : Prop :=
  ∀ i < k, dot ((blk (q + 1) i h).take q) y = (blk (q + 1) i h).getD q false

/-! ### Counting vectors orthogonal to a fixed nonzero vector -/

lemma card_filter_cube_succ (n : ℕ) (P : Str → Prop) [DecidablePred P] :
    ((Cube (n + 1)).filter P).card
      = ((Cube n).filter (fun l => P (false :: l))).card
        + ((Cube n).filter (fun l => P (true :: l))).card := by
  have h1 : Cube 1 = {[false], [true]} := by
    ext l
    simp only [mem_cube, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      match l, h with
      | [b], _ => cases b <;> simp
    · rintro (rfl | rfl) <;> simp
  have hn : n + 1 = 1 + n := by omega
  simp only [Finset.card_filter]
  rw [hn, sum_cube_append 1 n]
  rw [h1]
  rw [Finset.sum_insert (by simp)]
  simp

lemma card_dot_eq_zero : ∀ (d : Str), true ∈ d →
    ((Cube d.length).filter (fun a => dot a d = false)).card * 2 = 2 ^ d.length := by
  intro d
  induction d with
  | nil => intro h; simp at h
  | cons b d ih =>
      intro hmem
      rw [List.length_cons, card_filter_cube_succ]
      cases b with
      | true =>
          have h1 : ((Cube d.length).filter (fun l => dot (false :: l) (true :: d) = false)).card
              = ((Cube d.length).filter (fun l => dot l d = false)).card := by
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          have h2 : ((Cube d.length).filter (fun l => dot (true :: l) (true :: d) = false)).card
              = ((Cube d.length).filter (fun l => ¬ (dot l d = false))).card := by
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          rw [h1, h2, Finset.card_filter_add_card_filter_not, card_cube]
          ring
      | false =>
          have hmem' : true ∈ d := by simpa using hmem
          have h1 : ∀ (c : Bool), ((Cube d.length).filter
              (fun l => dot (c :: l) (false :: d) = false)).card
              = ((Cube d.length).filter (fun l => dot l d = false)).card := by
            intro c
            congr 1
            apply Finset.filter_congr
            intro l _
            simp
          rw [h1 false, h1 true]
          have := ih hmem'
          rw [pow_succ]
          omega

/-! ### Linearity of `dot` -/

lemma dot_xor : ∀ (a y y' : Str), y.length = y'.length →
    dot a (List.zipWith xor y y') = xor (dot a y) (dot a y') := by
  intro a
  induction a with
  | nil => intro y y' _; simp
  | cons c a ih =>
      intro y y' hlen
      match y, y' with
      | [], [] => simp
      | (b :: y), (b' :: y') =>
          simp only [List.zipWith_cons_cons, dot_cons]
          rw [ih y y' (by simpa using hlen)]
          cases c <;> cases b <;> cases b' <;> simp [Bool.xor_assoc, Bool.xor_comm,
            Bool.xor_left_comm]

lemma zipWith_xor_mem : ∀ (y y' : Str), y.length = y'.length → y ≠ y' →
    true ∈ List.zipWith xor y y' := by
  intro y
  induction y with
  | nil => intro y' hlen hne; cases y' <;> simp_all
  | cons b y ih =>
      intro y' hlen hne
      match y' with
      | (b' :: y') =>
          by_cases hb : b = b'
          · subst hb
            have hne' : y ≠ y' := by
              intro h; exact hne (by rw [h])
            have := ih y' (by simpa using hlen) hne'
            simp [this]
          · have : xor b b' = true := by cases b <;> cases b' <;> simp_all
            simp [this]

lemma zipWith_xor_length (y y' : Str) (h : y.length = y'.length) :
    (List.zipWith xor y y').length = y.length := by
  simp [h]

/-! ### The two counting lemmas -/

/-- Counting a single block: for a fixed `y`, exactly half of the blocks are "hit". -/
lemma card_block_hit (q : ℕ) (y : Str) (hy : y.length = q) :
    ((Cube (q + 1)).filter
      (fun u => dot (u.take q) y = u.getD q false)).card = 2 ^ q := by
  simp only [Finset.card_filter]
  rw [sum_cube_append q 1]
  have h1 : Cube 1 = {[false], [true]} := by
    ext l
    simp only [mem_cube, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      match l, h with
      | [b], _ => cases b <;> simp
    · rintro (rfl | rfl) <;> simp
  rw [h1]
  have : ∀ a ∈ Cube q, (∑ w ∈ ({[false], [true]} : Finset Str),
      if dot ((a ++ w).take q) y = (a ++ w).getD q false then (1 : ℕ) else 0) = 1 := by
    intro a ha
    rw [mem_cube] at ha
    rw [Finset.sum_insert (by simp)]
    have e1 : ∀ (c : Bool), ((a ++ [c]).take q) = a := by
      intro c; rw [← ha]; simp
    have e2 : ∀ (c : Bool), ((a ++ [c]).getD q false) = c := by
      intro c
      rw [← ha]
      simp [List.getD_eq_getElem?_getD]
    simp only [Finset.sum_singleton, e1, e2]
    cases hd : dot a y <;> simp
  rw [Finset.sum_congr rfl this]
  simp [card_cube]

/-- Counting a single block for two distinct points. -/
lemma card_block_hit2 (q : ℕ) (y y' : Str) (hy : y.length = q) (hy' : y'.length = q)
    (hne : y ≠ y') :
    ((Cube (q + 1)).filter
      (fun u => dot (u.take q) y = u.getD q false ∧
        dot (u.take q) y' = u.getD q false)).card * 2 = 2 ^ q := by
  simp only [Finset.card_filter]
  rw [sum_cube_append q 1]
  have h1 : Cube 1 = {[false], [true]} := by
    ext l
    simp only [mem_cube, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      match l, h with
      | [b], _ => cases b <;> simp
    · rintro (rfl | rfl) <;> simp
  rw [h1]
  have key : ∀ a ∈ Cube q, (∑ w ∈ ({[false], [true]} : Finset Str),
      if (dot ((a ++ w).take q) y = (a ++ w).getD q false ∧
          dot ((a ++ w).take q) y' = (a ++ w).getD q false) then (1 : ℕ) else 0)
      = (if dot a (List.zipWith xor y y') = false then 1 else 0) := by
    intro a ha
    rw [mem_cube] at ha
    rw [Finset.sum_insert (by simp)]
    have e1 : ∀ (c : Bool), ((a ++ [c]).take q) = a := by
      intro c; rw [← ha]; simp
    have e2 : ∀ (c : Bool), ((a ++ [c]).getD q false) = c := by
      intro c
      rw [← ha]
      simp [List.getD_eq_getElem?_getD]
    simp only [Finset.sum_singleton, e1, e2]
    rw [dot_xor a y y' (by rw [hy, hy'])]
    cases h : dot a y <;> cases h' : dot a y' <;> simp
  rw [Finset.sum_congr rfl key]
  have hlen : (List.zipWith xor y y').length = q := by
    rw [zipWith_xor_length y y' (by rw [hy, hy']), hy]
  have hmem : true ∈ List.zipWith xor y y' := zipWith_xor_mem y y' (by rw [hy, hy']) hne
  have := card_dot_eq_zero (List.zipWith xor y y') hmem
  rw [hlen] at this
  rw [← Finset.card_filter]
  exact this

/-- The general block-counting lemma for hash functions. -/
lemma card_hash_blocks (q k d : ℕ) (hk : k ≤ q + 4) (Q : Str → Prop) [DecidablePred Q]
    (hQ : ((Cube (q + 1)).filter Q).card * d = 2 ^ q) :
    ((Cube (hashLen q)).filter (fun h => ∀ i < k, Q (blk (q + 1) i h))).card * (d ^ k * 2 ^ k)
      = 2 ^ hashLen q := by
  set A := ((Cube (q + 1)).filter Q).card with hA
  have hfilter : ((Cube ((q + 4) * (q + 1))).filter
      (fun h => ∀ i < (q + 4), (i < k → Q (blk (q + 1) i h)))).card
      = ∏ i ∈ Finset.range (q + 4), ((Cube (q + 1)).filter (fun u => i < k → Q u)).card := by
    convert card_filter_blocks (q + 4) (q + 1) (fun i u => i < k → Q u) using 2
  have hset : ((Cube (hashLen q)).filter (fun h => ∀ i < k, Q (blk (q + 1) i h))).card
      = ((Cube ((q + 4) * (q + 1))).filter
          (fun h => ∀ i < (q + 4), (i < k → Q (blk (q + 1) i h)))).card := by
    congr 1
    ext h
    simp only [Finset.mem_filter, mem_cube, hashLen]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i _ hik => h2 i hik⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hik => h2 i (lt_of_lt_of_le hik hk) hik⟩
  have hcount : ∀ i ∈ Finset.range (q + 4),
      ((Cube (q + 1)).filter (fun u => i < k → Q u)).card = if i < k then A else 2 ^ (q + 1) := by
    intro i _
    by_cases hik : i < k
    · rw [if_pos hik, hA]
      congr 1
      ext u
      simp [hik]
    · rw [if_neg hik, ← card_cube (q + 1)]
      congr 1
      ext u
      simp [hik]
  have e1 : ∏ i ∈ Finset.Ico 0 k, (if i < k then A else 2 ^ (q + 1)) = A ^ k := by
    rw [Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_Ico] at hi; rw [if_pos hi.2])]
    simp
  have e2 : ∏ i ∈ Finset.Ico k (q + 4), (if i < k then A else 2 ^ (q + 1))
      = (2 ^ (q + 1)) ^ (q + 4 - k) := by
    rw [Finset.prod_congr rfl (fun i hi => by
      simp only [Finset.mem_Ico] at hi; rw [if_neg (Nat.not_lt.2 hi.1)])]
    simp
  rw [hset, hfilter, Finset.prod_congr rfl hcount, Finset.range_eq_Ico,
    ← Finset.prod_Ico_consecutive _ (Nat.zero_le k) hk, e1, e2]
  calc A ^ k * (2 ^ (q + 1)) ^ (q + 4 - k) * (d ^ k * 2 ^ k)
      = (A * d) ^ k * 2 ^ k * (2 ^ (q + 1)) ^ (q + 4 - k) := by rw [mul_pow]; ring
    _ = 2 ^ ((q + 1) * k) * (2 ^ (q + 1)) ^ (q + 4 - k) := by
        rw [hQ, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ = 2 ^ hashLen q := by
        rw [← pow_mul, ← pow_add, hashLen]
        congr 1
        obtain ⟨c, hc⟩ := Nat.le.dest hk
        have h4 : q + 4 - k = c := by omega
        rw [h4, ← hc]
        ring

/-- Uniformity: for a fixed `y`, the fraction of hash functions hitting `y` is `2^{-k}`. -/
theorem card_hit (q k : ℕ) (hk : k ≤ q + 4) (y : Str) (hy : y.length = q) :
    ((Cube (hashLen q)).filter (fun h => Hit q k h y)).card * 2 ^ k = 2 ^ hashLen q := by
  have := card_hash_blocks q k 1 hk (fun u => dot (u.take q) y = u.getD q false)
    (by rw [card_block_hit q y hy]; ring)
  simpa [Hit] using this

/-- Pairwise independence: for distinct `y ≠ y'` the fraction of hash functions hitting both
is `4^{-k}`. -/
theorem card_hit2 (q k : ℕ) (hk : k ≤ q + 4) (y y' : Str) (hy : y.length = q)
    (hy' : y'.length = q) (hne : y ≠ y') :
    ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y')).card * 2 ^ (2 * k)
      = 2 ^ hashLen q := by
  have hb := card_block_hit2 q y y' hy hy' hne
  have := card_hash_blocks q k 2 hk
    (fun u => dot (u.take q) y = u.getD q false ∧ dot (u.take q) y' = u.getD q false) hb
  have hpow : (2 : ℕ) ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← pow_add]; congr 1; ring
  rw [hpow] at this
  rw [← this]
  congr 2
  ext h
  simp only [Finset.mem_filter, Hit]
  constructor
  · rintro ⟨hm, h1, h2⟩; exact ⟨hm, fun i hi => ⟨h1 i hi, h2 i hi⟩⟩
  · rintro ⟨hm, h1⟩; exact ⟨hm, fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2⟩

/-! ### The isolation lemma -/

/-- **Valiant–Vazirani isolation lemma**.  If `S` is a nonempty set of `q`-bit strings and
`2^k` is within a factor of two of `4 |S|`, then for at least a `1/16` fraction of the hash
functions, `S` contains exactly one point hit by the hash, hence an odd number of them. -/
private lemma isolation_arith {Om K s X SN SN2 : ℕ}
    (m1 : SN * K = s * Om) (m2 : SN2 * (K * K) + s * Om = s * Om * K + s * s * Om)
    (pt : 2 * SN ≤ X + SN2) (hsk : 4 * s ≤ K) (hks : K ≤ 8 * s) (hs1 : 1 ≤ s)
    (hKpos : 0 < K) : Om ≤ 16 * X := by
  have h5 : 2 * SN * (K * K) ≤ (X + SN2) * (K * K) := Nat.mul_le_mul_right _ pt
  have h6 : 2 * SN * (K * K) = 2 * (s * Om) * K := by
    calc 2 * SN * (K * K) = 2 * (SN * K) * K := by ring
      _ = 2 * (s * Om) * K := by rw [m1]
  have h7 : (X + SN2) * (K * K) + s * Om = X * (K * K) + (s * Om * K + s * s * Om) := by
    rw [add_mul, add_assoc, m2]
  have h9 : 2 * (s * Om) * K + s * Om ≤ X * (K * K) + (s * Om * K + s * s * Om) := by
    rw [← h7, ← h6]
    exact Nat.add_le_add_right h5 _
  have h8 : s * Om * K + s * Om ≤ X * (K * K) + s * s * Om := by nlinarith [h9]
  have a1 : K * K ≤ 8 * s * K := Nat.mul_le_mul_right K hks
  have a2 : 4 * s * (4 * s) ≤ 4 * s * K := Nat.mul_le_mul_left (4 * s) hsk
  have hquad : K * K + 16 * (s * s) ≤ 16 * (s * K) + 16 * s := by nlinarith [a1, a2]
  have hq2 : (K * K + 16 * (s * s)) * Om ≤ (16 * (s * K) + 16 * s) * Om :=
    Nat.mul_le_mul_right Om hquad
  have h8' : 16 * (s * Om * K + s * Om) ≤ 16 * (X * (K * K) + s * s * Om) :=
    Nat.mul_le_mul_left 16 h8
  have hfin : Om * (K * K) ≤ 16 * X * (K * K) := by nlinarith [hq2, h8']
  exact Nat.le_of_mul_le_mul_right hfin (by positivity)

/-- **Valiant–Vazirani isolation lemma**.  If `S` is a nonempty set of `q`-bit strings and
`2^k` is within a factor of two of `4 |S|`, then for at least a `1/16` fraction of the hash
functions, `S` contains exactly one point hit by the hash, hence an odd number of them. -/
theorem isolation (q k : ℕ) (hk : k ≤ q + 4) (S : Finset Str) (hS : ∀ y ∈ S, y ∈ Cube q)
    (h1 : 4 * S.card ≤ 2 ^ k) (h2 : 2 ^ k ≤ 8 * S.card) (h3 : 1 ≤ S.card) :
    2 ^ hashLen q ≤ 16 * ((Cube (hashLen q)).filter
      (fun h => Odd ((S.filter (fun y => Hit q k h y)).card))).card := by
  classical
  have hq : ∀ y ∈ S, y.length = q := fun y hy => mem_cube.1 (hS y hy)
  -- first moment
  have moment1 : (∑ h ∈ Cube (hashLen q), (S.filter (fun y => Hit q k h y)).card) * 2 ^ k
      = S.card * 2 ^ hashLen q := by
    have e1 : (∑ h ∈ Cube (hashLen q), (S.filter (fun y => Hit q k h y)).card)
        = ∑ y ∈ S, ((Cube (hashLen q)).filter (fun h => Hit q k h y)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [e1, Finset.sum_mul, Finset.sum_congr rfl (fun y hy => card_hit q k hk y (hq y hy)),
      Finset.sum_const, smul_eq_mul]
  -- second moment
  have moment2 : (∑ h ∈ Cube (hashLen q), ((S.filter (fun y => Hit q k h y)).card) ^ 2)
        * (2 ^ k * 2 ^ k) + S.card * 2 ^ hashLen q
      = S.card * 2 ^ hashLen q * 2 ^ k + S.card * S.card * 2 ^ hashLen q := by
    have e2 : (∑ h ∈ Cube (hashLen q), ((S.filter (fun y => Hit q k h y)).card) ^ 2)
        = ∑ y ∈ S, ∑ y' ∈ S,
            ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y')).card := by
      have e1 : ∀ h : Str, ((S.filter (fun y => Hit q k h y)).card) ^ 2
          = ∑ y ∈ S, ∑ y' ∈ S, (if (Hit q k h y ∧ Hit q k h y') then (1 : ℕ) else 0) := by
        intro h
        rw [Finset.card_filter, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun y' _ => by
          by_cases hy : Hit q k h y <;> by_cases hy' : Hit q k h y' <;> simp [hy, hy']))
      rw [Finset.sum_congr rfl (fun h _ => e1 h), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y' _ => (Finset.card_filter _ _).symm)
    have inner : ∀ y ∈ S,
        (∑ y' ∈ S, ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y')).card)
            * (2 ^ k * 2 ^ k) + 2 ^ hashLen q
          = 2 ^ hashLen q * 2 ^ k + S.card * 2 ^ hashLen q := by
      intro y hy
      have hdiag : ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y)).card
          * (2 ^ k * 2 ^ k) = 2 ^ hashLen q * 2 ^ k := by
        have heq : ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y))
            = ((Cube (hashLen q)).filter (fun h => Hit q k h y)) := by
          ext h
          simp
        rw [heq, ← mul_assoc, card_hit q k hk y (hq y hy)]
      have hoff : ∀ y' ∈ S.erase y,
          ((Cube (hashLen q)).filter (fun h => Hit q k h y ∧ Hit q k h y')).card
            * (2 ^ k * 2 ^ k) = 2 ^ hashLen q := by
        intro y' hy'
        have hne : y ≠ y' := fun h => (Finset.mem_erase.1 hy').1 h.symm
        have h2k : (2 : ℕ) ^ k * 2 ^ k = 2 ^ (2 * k) := by rw [← pow_add]; congr 1; ring
        rw [h2k]
        exact card_hit2 q k hk y y' (hq y hy) (hq y' ((Finset.mem_erase.1 hy').2)) hne
      rw [← Finset.add_sum_erase S _ hy, add_mul, Finset.sum_mul,
        Finset.sum_congr rfl hoff, hdiag, Finset.sum_const, Finset.card_erase_of_mem hy,
        smul_eq_mul]
      have hs1 : S.card - 1 + 1 = S.card := by omega
      calc 2 ^ hashLen q * 2 ^ k + (S.card - 1) * 2 ^ hashLen q + 2 ^ hashLen q
          = 2 ^ hashLen q * 2 ^ k + ((S.card - 1) + 1) * 2 ^ hashLen q := by ring
        _ = 2 ^ hashLen q * 2 ^ k + S.card * 2 ^ hashLen q := by rw [hs1]
    have hsum := Finset.sum_congr rfl inner
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hsum
    rw [e2, hsum]
    ring
  -- pointwise inequality
  have ptwise : ∀ n : ℕ, 2 * n ≤ (if n = 1 then 1 else 0) + n ^ 2 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n <;> simp
    · have : 2 * n ≤ n ^ 2 := by nlinarith
      omega
  have sumpoint : 2 * (∑ h ∈ Cube (hashLen q), (S.filter (fun y => Hit q k h y)).card)
      ≤ ((Cube (hashLen q)).filter
            (fun h => (S.filter (fun y => Hit q k h y)).card = 1)).card
        + ∑ h ∈ Cube (hashLen q), ((S.filter (fun y => Hit q k h y)).card) ^ 2 := by
    rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun h _ => ptwise _)
  have hmain := isolation_arith moment1 moment2 sumpoint h1 h2 h3 (by positivity)
  refine le_trans hmain ?_
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro h hh
  simp only [Finset.mem_filter] at hh ⊢
  exact ⟨hh.1, by rw [hh.2]; exact odd_one⟩

end CS

import Mathlib

/-!
# Bit strings, cubes and blocks

Basic combinatorial infrastructure used in the formalisation of Toda's theorem:
the finite set `Cube n` of all bit strings of length `n`, block decompositions of
strings, and the product/sum factorisation over blocks.
-/

open Classical BigOperators

namespace CS

/-- Bit strings. -/
abbrev Str := List Bool

/-- The set of all bit strings of length `n`. -/
def Cube (n : ℕ) : Finset Str := Finset.image (fun f : Fin n → Bool => List.ofFn f) Finset.univ

lemma mem_cube {n : ℕ} {l : Str} : l ∈ Cube n ↔ l.length = n := by
  constructor
  · rintro h; simp [Cube] at h; obtain ⟨f, rfl⟩ := h; simp
  · intro h; subst h; simp [Cube]; exact ⟨fun i => l.get i, by simp⟩

lemma cube_zero : Cube 0 = {[]} := by ext l; simp [mem_cube]

lemma card_cube (n : ℕ) : (Cube n).card = 2 ^ n := by
  rw [Cube, Finset.card_image_of_injective _ (List.ofFn_injective)]; simp

lemma cube_nonempty (n : ℕ) : (Cube n).Nonempty :=
  ⟨List.replicate n false, mem_cube.2 (by simp)⟩

theorem sum_cube_append {M : Type} [AddCommMonoid M] (a b : ℕ) (F : Str → M) :
    ∑ v ∈ Cube (a + b), F v = ∑ u ∈ Cube a, ∑ w ∈ Cube b, F (u ++ w) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun v => (v.take a, v.drop a)) (j := fun p => p.1 ++ p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro v hv; rw [mem_cube] at hv; simp [Finset.mem_product, mem_cube, hv]
  · rintro ⟨u, w⟩ h; simp [Finset.mem_product, mem_cube] at h; simp [mem_cube, h.1, h.2]
  · intro v hv; simp
  · rintro ⟨u, w⟩ h; simp [Finset.mem_product, mem_cube] at h; simp [h.1]
  · intro v hv; simp

/-- The `j`-th block of length `B` of a string. -/
def blk (B j : ℕ) (v : Str) : Str := (v.drop (j * B)).take B

lemma blk_zero_append {B : ℕ} {u w : Str} (hu : u.length = B) : blk B 0 (u ++ w) = u := by
  simp [blk, ← hu]

lemma blk_succ_append {u w : Str} {B j : ℕ} (hu : u.length = B) :
    blk B (j + 1) (u ++ w) = blk B j w := by
  unfold blk
  have h1 : (j + 1) * B = u.length + j * B := by rw [hu]; ring
  rw [h1, List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

lemma blk_mem_cube {B j T : ℕ} {v : Str} (hv : v ∈ Cube (T * B)) (hj : j < T) :
    blk B j v ∈ Cube B := by
  rw [mem_cube] at hv ⊢
  simp only [blk, List.length_take, List.length_drop, hv]
  have h2 : j * B + B ≤ T * B := by
    calc j * B + B = (j + 1) * B := by ring
      _ ≤ T * B := Nat.mul_le_mul_right _ hj
  omega

/-- Factorisation of a sum of block-wise products over a cube. -/
theorem prod_sum_blocks {M : Type} [CommSemiring M] (B : ℕ) :
    ∀ (T : ℕ) (g : ℕ → Str → M),
    ∑ v ∈ Cube (T * B), ∏ j ∈ Finset.range T, g j (blk B j v)
      = ∏ j ∈ Finset.range T, ∑ u ∈ Cube B, g j u := by
  intro T
  induction T with
  | zero => intro g; simp [cube_zero]
  | succ T ih =>
      intro g
      have h : (T + 1) * B = B + T * B := by ring
      calc ∑ v ∈ Cube ((T + 1) * B), ∏ j ∈ Finset.range (T + 1), g j (blk B j v)
          = ∑ u ∈ Cube B, ∑ w ∈ Cube (T * B),
              ∏ j ∈ Finset.range (T + 1), g j (blk B j (u ++ w)) := by
            rw [h, sum_cube_append]
        _ = ∑ u ∈ Cube B, ∑ w ∈ Cube (T * B),
              (g 0 u * ∏ j ∈ Finset.range T, g (j + 1) (blk B j w)) := by
            refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w _ => ?_))
            rw [mem_cube] at hu
            rw [Finset.prod_range_succ', blk_zero_append hu, mul_comm]
            congr 1
            exact Finset.prod_congr rfl (fun j _ => by rw [blk_succ_append hu])
        _ = (∑ u ∈ Cube B, g 0 u) *
              (∑ w ∈ Cube (T * B), ∏ j ∈ Finset.range T, g (j + 1) (blk B j w)) := by
            rw [Finset.sum_mul_sum]
        _ = (∑ u ∈ Cube B, g 0 u) * ∏ j ∈ Finset.range T, ∑ u ∈ Cube B, g (j + 1) u := by
            rw [ih (fun j => g (j + 1))]
        _ = ∏ j ∈ Finset.range (T + 1), ∑ u ∈ Cube B, g j u := by
            rw [Finset.prod_range_succ']; ring

/-- Counting version of `prod_sum_blocks`. -/
theorem card_filter_blocks (T B : ℕ) (P : ℕ → Str → Prop) [∀ j, DecidablePred (P j)] :
    ((Cube (T * B)).filter (fun v => ∀ j < T, P j (blk B j v))).card
      = ∏ j ∈ Finset.range T, ((Cube B).filter (P j)).card := by
  have h1 : ∀ v : Str, (if (∀ j < T, P j (blk B j v)) then (1 : ℕ) else 0)
      = ∏ j ∈ Finset.range T, (if P j (blk B j v) then (1 : ℕ) else 0) := by
    intro v
    rw [Finset.prod_boole]
    congr 1
    simp
  simp only [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun v _ => h1 v), prod_sum_blocks B T
      (fun j u => if P j u then (1 : ℕ) else 0)]

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

