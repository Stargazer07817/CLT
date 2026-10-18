import LeanClt.Elementary.Orbits

/-!
# Flow identity, doubling, and merging classes (elementary layer)

* `hit` under one backward step: if `G a = n` and `a ≠ b`, then `a` reaches `b` iff `n` does,
  and `τ(a) = τ(n) + 1`. With `a = 2n` this is the doubling rule used in Lemma 6.5 [`lem:sampling`]
  and in the proof of Theorem 1.1.
* **Proposition 7.3 [`prop:flow`] (set level).** For a non-periodic `n > 0`,
  `P_T(n) = {n} ⊔ P_T(2n) ⊔ P_T((n-1)/3)`, the last part present only when `n ≡ 4 (mod 6)`.
* Merging classes form an equivalence relation, and every class contains an integer
  prime to 3 (proof of Theorem 1.3(iii)).
-/

open Function

namespace CollatzCLT

/-! ## One backward step and the doubling rule -/

/-- If `G a = n` and `a ≠ b`, then `a` reaches `b` iff `n` does. -/
lemma reaches_iff_of_step {G : ℕ → ℕ} {a n b : ℕ} (hstep : G a = n) (hab : a ≠ b) :
    (∃ k, G^[k] a = b) ↔ (∃ k, G^[k] n = b) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact absurd hk hab
    | succ k => exact ⟨k, by rwa [iterate_succ_apply, hstep] at hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [iterate_succ_apply, hstep, hk]⟩

/-- If `G a = n`, `a ≠ b` and `n` reaches `b`, then `τ_b(a) = τ_b(n) + 1`. -/
lemma hit_of_step {G : ℕ → ℕ} {a n b : ℕ} (hstep : G a = n) (hab : a ≠ b)
    (hn : ∃ k, G^[k] n = b) : hit G b a = hit G b n + 1 := by
  have ha : ∃ k, G^[k] a = b := (reaches_iff_of_step hstep hab).mpr hn
  apply le_antisymm
  · apply hit_le
    rw [iterate_succ_apply, hstep, iterate_hit hn]
  · have h := iterate_hit ha
    -- `τ(a) ≥ 1` since `a ≠ b`; one step later we are at `n`
    obtain ⟨k, hk⟩ : ∃ k, hit G b a = k + 1 := by
      rcases Nat.exists_eq_succ_of_ne_zero (n := hit G b a) (by
        intro h0; rw [h0] at h; exact hab h) with ⟨k, hk⟩
      exact ⟨k, hk⟩
    rw [hk, iterate_succ_apply, hstep] at h
    rw [hk]
    exact Nat.succ_le_succ (hit_le h)

/-- Doubling, raw clock: for `2n ≠ b`, `2n ∈ P_T(b) ↔ n ∈ P_T(b)` (for `n > 0`). -/
lemma two_mul_mem_predT_iff {n b : ℕ} (hn : 0 < n) (hb : 2 * n ≠ b) :
    2 * n ∈ Pred T b ↔ n ∈ Pred T b := by
  simp only [Pred, Set.mem_ofPred_eq, reaches_iff_of_step (T_two_mul n) hb]
  constructor <;> rintro ⟨_, h⟩ <;> exact ⟨by omega, h⟩

/-- Doubling, raw clock: `τ_{T,b}(2n) = τ_{T,b}(n) + 1` when `2n ≠ b` and `n ∈ P_T(b)`. -/
lemma hit_T_two_mul {n b : ℕ} (hb : 2 * n ≠ b) (hn : n ∈ Pred T b) :
    hit T b (2 * n) = hit T b n + 1 :=
  hit_of_step (T_two_mul n) hb hn.2

/-- Doubling, shortcut clock. -/
lemma two_mul_mem_predF_iff {n b : ℕ} (hn : 0 < n) (hb : 2 * n ≠ b) :
    2 * n ∈ Pred F b ↔ n ∈ Pred F b := by
  simp only [Pred, Set.mem_ofPred_eq, reaches_iff_of_step (F_two_mul n) hb]
  constructor <;> rintro ⟨_, h⟩ <;> exact ⟨by omega, h⟩

/-- Doubling, shortcut clock: `τ_{F,b}(2n) = τ_{F,b}(n) + 1` when `2n ≠ b`, `n ∈ P_F(b)`. -/
lemma hit_F_two_mul {n b : ℕ} (hb : 2 * n ≠ b) (hn : n ∈ Pred F b) :
    hit F b (2 * n) = hit F b n + 1 :=
  hit_of_step (F_two_mul n) hb hn.2

/-! ## The flow identity (Proposition 7.3 [`prop:flow`], set level) -/

/-- `n` is a periodic point of `T`. -/
def IsPeriodic (n : ℕ) : Prop := ∃ p, 0 < p ∧ T^[p] n = n

/-- The odd preimage branch of `n`: `P_T((n-1)/3)` if `n ≡ 4 (mod 6)`, else empty. -/
def oddBranch (n : ℕ) : Set ℕ := if n % 6 = 4 then Pred T ((n - 1) / 3) else ∅

/-- If `n ≡ 4 (mod 6)` then `(n-1)/3` is odd and `T((n-1)/3) = n`. -/
lemma T_odd_preimage {n : ℕ} (h : n % 6 = 4) : T ((n - 1) / 3) = n := by
  have hodd : ¬ Even ((n - 1) / 3) := by
    rw [Nat.not_even_iff_odd]; exact ⟨n / 6, by omega⟩
  rw [T_of_odd hodd]; omega

/-- **Proposition 7.3 [`prop:flow`], decomposition.** For every `n > 0` (periodic or not),
`P_T(n) = {n} ∪ P_T(2n) ∪ oddBranch n`. Disjointness, which needs non-periodicity, is
`pred_flow_disjoint`. -/
theorem pred_flow_eq {n : ℕ} (hn : 0 < n) :
    Pred T n = {n} ∪ Pred T (2 * n) ∪ oddBranch n := by
  ext m
  simp only [Set.mem_union, Set.mem_singleton_iff, oddBranch]
  constructor
  · rintro ⟨hm, k, hk⟩
    cases k with
    | zero => left; left; simpa using hk
    | succ k =>
      rw [iterate_succ_apply'] at hk
      rcases T_eq_iff.mp hk with h | ⟨hodd, h⟩
      · left; right; exact ⟨hm, k, h⟩
      · right
        have h6 : n % 6 = 4 := by
          rw [Nat.not_even_iff_odd] at hodd; obtain ⟨q, hq⟩ := hodd; omega
        simp only [h6, ↓reduceIte]
        exact ⟨hm, k, by omega⟩
  · rintro ((rfl | ⟨hm, k, hk⟩) | h)
    · exact ⟨hn, 0, rfl⟩
    · exact ⟨hm, k + 1, by rw [iterate_succ_apply', hk, T_two_mul]⟩
    · split_ifs at h with h6
      · obtain ⟨hm, k, hk⟩ := h
        exact ⟨hm, k + 1, by rw [iterate_succ_apply', hk, T_odd_preimage h6]⟩
      · exact h.elim

/-- If an orbit visits `y` and then (at a different time) `y'` with `T y = T y' = n`,
the two visits to `n` force `n` to be periodic unless they happen at the same time. -/
lemma periodic_of_two_visits {m n i j : ℕ} (hi : T^[i] m = n) (hj : T^[j] m = n)
    (hij : i < j) : IsPeriodic n := by
  refine ⟨j - i, by omega, ?_⟩
  rw [← hi, ← iterate_add_apply, Nat.sub_add_cancel hij.le, hj, hi]

/-- **Proposition 7.3 [`prop:flow`], disjointness.** For non-periodic `n > 0` the three parts are
pairwise disjoint. -/
theorem pred_flow_disjoint {n : ℕ} (hn : 0 < n) (hper : ¬ IsPeriodic n) :
    n ∉ Pred T (2 * n) ∧ n ∉ oddBranch n ∧ Disjoint (Pred T (2 * n)) (oddBranch n) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, hk⟩
    exact hper (periodic_of_two_visits (i := 0) (j := k + 1) rfl
      (by rw [iterate_succ_apply', hk, T_two_mul]) (by omega))
  · intro h
    simp only [oddBranch] at h
    split_ifs at h with h6
    · obtain ⟨_, k, hk⟩ := h
      exact hper (periodic_of_two_visits (i := 0) (j := k + 1) rfl
        (by rw [iterate_succ_apply', hk, T_odd_preimage h6]) (by omega))
    · exact h
  · rw [Set.disjoint_left]
    intro m h1 h2
    simp only [oddBranch] at h2
    split_ifs at h2 with h6
    · obtain ⟨_, i, hi⟩ := h1
      obtain ⟨_, j, hj⟩ := h2
      have hi' : T^[i + 1] m = n := by rw [iterate_succ_apply', hi, T_two_mul]
      have hj' : T^[j + 1] m = n := by rw [iterate_succ_apply', hj, T_odd_preimage h6]
      rcases lt_trichotomy i j with h | rfl | h
      · exact hper (periodic_of_two_visits hi' hj' (by omega))
      · rw [hi] at hj; omega
      · exact hper (periodic_of_two_visits hj' hi' (by omega))
    · exact h2

/-! ## Merging classes -/

/-- `m` and `n` merge if their orbits meet: `T^i(m) = T^j(n)` for some `i, j`. -/
def Merge (m n : ℕ) : Prop := ∃ i j, T^[i] m = T^[j] n

/-- Merging is an equivalence relation (Theorem 1.3(iii)). -/
theorem merge_equivalence : Equivalence Merge where
  refl n := ⟨0, 0, rfl⟩
  symm := fun ⟨i, j, h⟩ => ⟨j, i, h.symm⟩
  trans := by
    rintro a b c ⟨i, j, h1⟩ ⟨k, l, h2⟩
    refine ⟨k + i, j + l, ?_⟩
    rw [iterate_add_apply, h1, ← iterate_add_apply, add_comm k j, iterate_add_apply, h2,
      ← iterate_add_apply]

/-- A point merges with each of its iterates. -/
lemma merge_iterate (n k : ℕ) : Merge n (T^[k] n) := ⟨k, 0, rfl⟩

/-- Every positive integer has an iterate not divisible by 3 (so every merging class
contains an integer prime to 3; used in Theorem 1.3(iii) and Corollary 1.5 [`cor:dichotomy`]). -/
theorem exists_iterate_not_three_dvd {n : ℕ} (hn : 0 < n) : ∃ k, ¬ 3 ∣ T^[k] n := by
  obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  -- halve `e` times to reach the odd part `u`, then one odd step gives `3u + 1`
  have hhalve : T^[e] (2 ^ e * u) = u := by
    clear hn
    induction e with
    | zero => simp
    | succ e ih =>
      rw [iterate_succ_apply, pow_succ, mul_comm (2 ^ e) 2, mul_assoc, T_two_mul]
      exact ih
  refine ⟨e + 1, ?_⟩
  rw [iterate_succ_apply', hhalve, T_of_odd (Nat.not_even_iff_odd.mpr hu)]
  omega

end CollatzCLT
