import LeanClt.Defs

/-!
# Orbit combinatorics (elementary layer)

Elementary facts about the maps `T` and `F` used throughout the paper:
* how `T` and `F` act on even and odd inputs, and the preimages of a point under `T`;
* basic properties of the hitting time `hit`;
* the dyadic ray `P_T(b) = {2^j b}` when `3 ∣ b` (remark after Theorem 1.1);
* periodic points are never divisible by 3 (§9);
* the inclusions `P_T(2b) ⊆ P_F(b) ⊆ P_T(b)` (proof of Theorem 1.1, §6.5).
-/

open Function

namespace CollatzCLT

/-! ## How the maps act -/

lemma T_of_even {n : ℕ} (h : Even n) : T n = n / 2 := by simp [T, h]

lemma T_of_odd {n : ℕ} (h : ¬ Even n) : T n = 3 * n + 1 := by simp [T, h]

lemma F_of_even {n : ℕ} (h : Even n) : F n = n / 2 := by simp [F, h]

lemma F_of_odd {n : ℕ} (h : ¬ Even n) : F n = (3 * n + 1) / 2 := by simp [F, h]

@[simp] lemma T_two_mul (n : ℕ) : T (2 * n) = n := by
  rw [T_of_even (even_two_mul n)]; omega

@[simp] lemma F_two_mul (n : ℕ) : F (2 * n) = n := by
  rw [F_of_even (even_two_mul n)]; omega

/-- On an odd input, one shortcut step is two raw steps. -/
lemma F_eq_T_T_of_odd {n : ℕ} (h : ¬ Even n) : F n = T (T n) := by
  have h2 : Even (3 * n + 1) := by
    rcases Nat.not_even_iff_odd.mp h with ⟨k, rfl⟩
    exact ⟨3 * k + 2, by ring⟩
  rw [F_of_odd h, T_of_odd h, T_of_even h2]

/-- On an even input, one shortcut step is one raw step. -/
lemma F_eq_T_of_even {n : ℕ} (h : Even n) : F n = T n := by
  rw [F_of_even h, T_of_even h]

/-- **Preimages under `T`.** `T m = n` iff `m = 2n`, or `m` is odd with
`3m + 1 = n`. -/
lemma T_eq_iff {m n : ℕ} :
    T m = n ↔ m = 2 * n ∨ (¬ Even m ∧ 3 * m + 1 = n) := by
  by_cases hm : Even m
  · rw [T_of_even hm]
    obtain ⟨k, rfl⟩ := hm
    constructor
    · intro h; left; omega
    · rintro (h | ⟨h, _⟩)
      · omega
      · exact absurd ⟨k, rfl⟩ h
  · rw [T_of_odd hm]
    constructor
    · intro h; exact Or.inr ⟨hm, h⟩
    · rintro (h | ⟨_, h⟩)
      · exact absurd ⟨n, by omega⟩ hm
      · exact h

/-! ## Hitting times -/

lemma iterate_hit {G : ℕ → ℕ} {b n : ℕ} (h : ∃ k, G^[k] n = b) : G^[hit G b n] n = b :=
  Nat.sInf_mem h

lemma hit_le {G : ℕ → ℕ} {b n k : ℕ} (h : G^[k] n = b) : hit G b n ≤ k :=
  Nat.sInf_le h

lemma lt_hit {G : ℕ → ℕ} {b n k : ℕ} (hk : k < hit G b n) : G^[k] n ≠ b :=
  fun h => absurd (hit_le h) (not_le.mpr hk)

/-! ## Multiples of 3: the dyadic ray -/

/-- If `T^[k] m = b` and `3 ∣ b` (with `b > 0`), then `m = 2^k b`: a multiple of 3 is
reached only by halving. -/
lemma eq_pow_mul_of_iterate_eq_of_three_dvd :
    ∀ (k : ℕ) {m b : ℕ}, 0 < b → 3 ∣ b → T^[k] m = b → m = 2 ^ k * b := by
  intro k
  induction k with
  | zero => intro m b _ _ h; simpa using h
  | succ k ih =>
    intro m b hb h3 h
    rw [iterate_succ_apply'] at h
    -- the state before `b` is a preimage of `b`; it cannot be odd since `3m'+1 ≢ 0 (mod 3)`
    have hpre := T_eq_iff.mp h
    rcases hpre with hpre | ⟨_, hpre⟩
    · have := ih (by omega) (dvd_mul_of_dvd_right h3 2) hpre
      rw [this, pow_succ]; ring
    · omega

/-- **Remark after Theorem 1.1.** If `3 ∣ b`, then `P_T(b)` is the dyadic ray `{2^j b}`. -/
theorem pred_of_three_dvd {b : ℕ} (hb : 0 < b) (h3 : 3 ∣ b) :
    Pred T b = {n | ∃ j, n = 2 ^ j * b} := by
  ext n
  constructor
  · rintro ⟨_, k, hk⟩
    exact ⟨k, eq_pow_mul_of_iterate_eq_of_three_dvd k hb h3 hk⟩
  · rintro ⟨j, rfl⟩
    refine ⟨by positivity, j, ?_⟩
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iterate_succ_apply, pow_succ, mul_comm (2 ^ j) 2, mul_assoc, T_two_mul]
      exact ih

/-- Periodic points of `T` are not divisible by 3 (§9). -/
theorem not_three_dvd_of_periodic {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (hper : T^[p] n = n) :
    ¬ 3 ∣ n := by
  intro h3
  have h := eq_pow_mul_of_iterate_eq_of_three_dvd p hn h3 hper
  have : 2 ^ p * n > 1 * n := by
    apply Nat.mul_lt_mul_of_pos_right _ hn
    exact Nat.one_lt_two_pow (by omega)
  omega

/-! ## Comparing the raw and shortcut orbits -/

/-- Every shortcut-orbit state is a raw-orbit state. -/
lemma exists_T_iterate_eq_F_iterate (n : ℕ) : ∀ j, ∃ k, T^[k] n = F^[j] n := by
  intro j
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    by_cases he : Even (F^[j] n)
    · refine ⟨k + 1, ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', hk, F_eq_T_of_even he]
    · refine ⟨k + 2, ?_⟩
      rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', hk,
        F_eq_T_T_of_odd he]

/-- Every raw-orbit state is visited by the shortcut orbit, or else (if it is the
skipped even state `3x+1`) the next raw state is. -/
lemma exists_F_iterate_eq_T_iterate (n : ℕ) :
    ∀ k, ∃ j, F^[j] n = T^[k] n ∨ F^[j] n = T^[k + 1] n := by
  intro k
  induction k with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ k ih =>
    obtain ⟨j, hj | hj⟩ := ih
    · by_cases he : Even (T^[k] n)
      · refine ⟨j + 1, Or.inl ?_⟩
        rw [iterate_succ_apply', iterate_succ_apply', hj, F_eq_T_of_even he]
      · refine ⟨j + 1, Or.inr ?_⟩
        rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', hj,
          F_eq_T_T_of_odd he]
    · exact ⟨j, Or.inl hj⟩

/-- `P_F(b) ⊆ P_T(b)`: the shortcut orbit is a subsequence of the raw orbit. -/
theorem predF_subset_predT (b : ℕ) : Pred F b ⊆ Pred T b := by
  rintro n ⟨hn, j, hj⟩
  obtain ⟨k, hk⟩ := exists_T_iterate_eq_F_iterate n j
  exact ⟨hn, k, hk.trans hj⟩

/-- `P_T(2b) ⊆ P_F(b)`: a raw orbit visiting `2b` has a shortcut orbit visiting `b`. -/
theorem predT_two_mul_subset_predF (b : ℕ) : Pred T (2 * b) ⊆ Pred F b := by
  rintro n ⟨hn, k, hk⟩
  refine ⟨hn, ?_⟩
  obtain ⟨j, hj | hj⟩ := exists_F_iterate_eq_T_iterate n k
  · refine ⟨j + 1, ?_⟩
    rw [iterate_succ_apply', hj, hk, F_two_mul]
  · refine ⟨j, ?_⟩
    rw [hj, iterate_succ_apply', hk, T_two_mul]

end CollatzCLT
