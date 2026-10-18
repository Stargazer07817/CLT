import LeanClt.Elementary.Flow

/-!
# The Syracuse map inside the raw orbit

For odd `n` with `v = v₂(3n+1)`, the raw orbit runs `n → 3n+1 → (3n+1)/2 → ⋯ → (3n+1)/2^v = U(n)`.
The intermediate states are even, and `U(n)` is odd. Consequently, for odd `b`,
`P_U(b) = Odd ∩ P_T(b)` (stated in Theorem 1.1(iii): "`P_U(b)` is the set of odd members of
`P_T(b)`").
-/

open Function

namespace CollatzCLT

/-- `U n` is odd (for every `n`): dividing `3n+1 > 0` by its full power of `2`. -/
lemma U_odd (n : ℕ) : Odd (U n) := by
  unfold U
  have hpos : 0 < 3 * n + 1 := by omega
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) := by omega
  have hdvd : 2 ^ padicValNat 2 (3 * n + 1) ∣ 3 * n + 1 := pow_padicValNat_dvd
  obtain ⟨k, hk⟩ := h2
  have : 2 ^ (padicValNat 2 (3 * n + 1) + 1) ∣ 3 * n + 1 := by
    refine ⟨k, ?_⟩
    rw [pow_succ, mul_assoc, ← hk, Nat.mul_div_cancel' hdvd]
  exact pow_succ_padicValNat_not_dvd hpos.ne' this

/-- For odd `n`, `v₂(3n+1) ≥ 1`. -/
lemma one_le_padicValNat_of_odd {n : ℕ} (hn : Odd n) : 1 ≤ padicValNat 2 (3 * n + 1) := by
  have h2 : 2 ∣ 3 * n + 1 := by obtain ⟨k, rfl⟩ := hn; exact ⟨3 * k + 2, by ring⟩
  exact one_le_padicValNat_of_dvd (by omega) h2

/-- If `2^{i+1} ∣ N` then `N / 2^i` is even. -/
lemma even_div_pow_of_dvd {N i : ℕ} (h : 2 ^ (i + 1) ∣ N) : Even (N / 2 ^ i) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [hk, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  ring

/-- The raw orbit of an odd `n` during its halving run: `T^j(n) = (3n+1)/2^{j-1}` for
`1 ≤ j ≤ v₂(3n+1) + 1`. -/
lemma T_iterate_odd {n : ℕ} (hn : Odd n) :
    ∀ j, 1 ≤ j → j ≤ padicValNat 2 (3 * n + 1) + 1 → T^[j] n = (3 * n + 1) / 2 ^ (j - 1) := by
  intro j hj1 hj2
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [T_of_odd (Nat.not_even_iff_odd.mpr hn)]
    rw [iterate_succ_apply', ih hj (by omega)]
    -- the state `(3n+1)/2^{j-1}` is even because `j ≤ v`
    have hdvd : 2 ^ j ∣ 3 * n + 1 :=
      (pow_dvd_pow 2 (by omega : j ≤ padicValNat 2 (3 * n + 1))).trans pow_padicValNat_dvd
    have heven : Even ((3 * n + 1) / 2 ^ (j - 1)) := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simpa using even_div_pow_of_dvd hdvd
    rw [T_of_even heven, Nat.div_div_eq_div_mul, ← pow_succ]
    congr 2; omega

/-- For odd `n`, `T^{v+1}(n) = U(n)` with `v = v₂(3n+1)`. -/
lemma T_iterate_eq_U {n : ℕ} (hn : Odd n) :
    T^[padicValNat 2 (3 * n + 1) + 1] n = U n := by
  rw [T_iterate_odd hn _ (by omega) le_rfl]
  simp [U]

/-- During the halving run (`1 ≤ j ≤ v`) the raw states are even. -/
lemma T_iterate_even_of_lt {n : ℕ} (hn : Odd n) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ padicValNat 2 (3 * n + 1)) : Even (T^[j] n) := by
  rw [T_iterate_odd hn j hj1 (by omega)]
  have hdvd : 2 ^ j ∣ 3 * n + 1 :=
    (pow_dvd_pow 2 hj2).trans pow_padicValNat_dvd
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simpa using even_div_pow_of_dvd hdvd

/-- Every Syracuse iterate of an odd `n` is a raw iterate. -/
lemma exists_T_iterate_eq_U_iterate {n : ℕ} (hn : Odd n) : ∀ k, ∃ m, T^[m] n = U^[k] n := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    have hodd : Odd (U^[k] n) := by
      cases k with
      | zero => simpa using hn
      | succ k => rw [iterate_succ_apply']; exact U_odd _
    refine ⟨padicValNat 2 (3 * U^[k] n + 1) + 1 + m, ?_⟩
    rw [iterate_add_apply, hm, T_iterate_eq_U hodd, iterate_succ_apply']

/-- Every odd raw iterate of an odd `n` is a Syracuse iterate. -/
lemma exists_U_iterate_eq_T_iterate :
    ∀ m n, Odd n → Odd (T^[m] n) → ∃ k, U^[k] n = T^[m] n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hn hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · exact ⟨0, rfl⟩
    set v := padicValNat 2 (3 * n + 1)
    by_cases hle : m ≤ v
    · exact absurd (T_iterate_even_of_lt hn hmpos hle) (Nat.not_even_iff_odd.mpr hm)
    · -- after `v + 1` raw steps we are at `U n`
      have hsplit : T^[m] n = T^[m - (v + 1)] (U n) := by
        rw [← T_iterate_eq_U hn, ← iterate_add_apply]; congr 1; omega
      rw [hsplit] at hm ⊢
      obtain ⟨k, hk⟩ := ih (m - (v + 1)) (by omega) (U n) (U_odd n) hm
      exact ⟨k + 1, by rw [iterate_succ_apply, hk]⟩

/-- **`P_U(b)` is the odd part of `P_T(b)`** for odd `b`. -/
theorem predU_eq {b : ℕ} (hb : Odd b) : PredU b = {n | Odd n} ∩ Pred T b := by
  ext n
  simp only [PredU, Pred, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn0, hn, k, hk⟩
    obtain ⟨m, hm⟩ := exists_T_iterate_eq_U_iterate hn k
    exact ⟨hn, hn0, m, hm.trans hk⟩
  · rintro ⟨hn, hn0, m, hm⟩
    obtain ⟨k, hk⟩ := exists_U_iterate_eq_T_iterate m n hn (by rw [hm]; exact hb)
    exact ⟨hn0, hn, k, hk.trans hm⟩

end CollatzCLT
