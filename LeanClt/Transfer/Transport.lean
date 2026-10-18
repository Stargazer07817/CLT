import LeanClt.Transfer.Defs
import LeanClt.Elementary.Syracuse

/-!
# §6.5: the transport property for the three clocks

For an odd source `N` whose early segment `N, U(N), …, U^r(N) = M` stays above `x > b` (the
first passage `T_x(N)` comes after `M`, since `m ≥ 1`), every raw and shortcut state of the
segment also stays above `x`. So the segment does not visit `b`, membership in the predecessor set
transfers between `N` and `M`, and hitting times add:
`τ_T(N) = S + r + τ_T(M)`, `τ_F(N) = S + τ_F(M)`, `τ_U(N) = r + τ_U(M)`.
-/

open Function

namespace CollatzCLT

/-! ## Shifting along a segment that avoids the target -/

lemma pred_shift {G : ℕ → ℕ} {N M b k : ℕ} (hk : G^[k] N = M) (hav : ∀ j ≤ k, G^[j] N ≠ b)
    (hN : 0 < N) (hM : 0 < M) :
    (N ∈ Pred G b ↔ M ∈ Pred G b) ∧ (N ∈ Pred G b → hit G b N = k + hit G b M) := by
  have back : ∀ i, G^[i] N = b → k < i ∧ G^[i - k] M = b := by
    intro i hi
    have hki : k < i := by
      by_contra h; push Not at h; exact hav i h hi
    refine ⟨hki, ?_⟩
    rw [← hk, ← iterate_add_apply, show i - k + k = i by omega, hi]
  refine ⟨⟨fun ⟨_, i, hi⟩ => ⟨hM, i - k, (back i hi).2⟩,
    fun ⟨_, i, hi⟩ => ⟨hN, i + k, by rw [iterate_add_apply, hk, hi]⟩⟩, ?_⟩
  rintro ⟨_, i, hi⟩
  have hM' : ∃ j, G^[j] M = b := ⟨i - k, (back i hi).2⟩
  have h1 : G^[hit G b N] N = b := iterate_hit ⟨i, hi⟩
  obtain ⟨hk1, h2⟩ := back _ h1
  have h3 : hit G b M ≤ hit G b N - k := hit_le h2
  have h4 : hit G b N ≤ hit G b M + k := hit_le (by rw [iterate_add_apply, hk, iterate_hit hM'])
  omega

/-! ## Raw and shortcut blocks -/

/-- The shortcut orbit of an odd `n`: `F^j(n) = (3n+1)/2^j` for `1 ≤ j ≤ v₂(3n+1)`. -/
lemma F_iterate_odd {n : ℕ} (hn : Odd n) :
    ∀ j, 1 ≤ j → j ≤ padicValNat 2 (3 * n + 1) → F^[j] n = (3 * n + 1) / 2 ^ j := by
  intro j hj1 hj2
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [F_of_odd (Nat.not_even_iff_odd.mpr hn)]
    rw [iterate_succ_apply', ih hj (by omega)]
    have hdvd : 2 ^ (j + 1) ∣ 3 * n + 1 :=
      (pow_dvd_pow 2 (by omega : j + 1 ≤ padicValNat 2 (3 * n + 1))).trans pow_padicValNat_dvd
    rw [F_of_even (even_div_pow_of_dvd hdvd), Nat.div_div_eq_div_mul, ← pow_succ]

lemma F_iterate_eq_U {n : ℕ} (hn : Odd n) : F^[padicValNat 2 (3 * n + 1)] n = U n := by
  rw [F_iterate_odd hn _ (one_le_padicValNat_of_odd hn) le_rfl]; rfl

lemma odd_U_iterate {N : ℕ} (hN : Odd N) (i : ℕ) : Odd (U^[i] N) := by
  cases i with
  | zero => simpa using hN
  | succ i => rw [iterate_succ_apply']; exact U_odd _

/-- The raw orbit over `r` odd blocks: `T^{S_r + r}(N) = U^r(N)`, and every intermediate raw state
is at least some `U^i(N)`, `i ≤ r`. -/
lemma T_blocks {N : ℕ} (hN : Odd N) (r : ℕ) :
    T^[wsum (vword N) r + r] N = U^[r] N ∧
      ∀ j ≤ wsum (vword N) r + r, ∃ i ≤ r, U^[i] N ≤ T^[j] N := by
  induction r with
  | zero => exact ⟨by simp [wsum], fun j hj => ⟨0, le_rfl, by simp [wsum] at hj; subst hj; simp⟩⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    set z := U^[r] N with hz
    have hzo : Odd z := odd_U_iterate hN r
    have hv : vword N r = padicValNat 2 (3 * z + 1) := rfl
    have hw : wsum (vword N) (r + 1) + (r + 1) = (wsum (vword N) r + r) + (vword N r + 1) := by
      simp only [wsum, Finset.sum_range_succ]; ring
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hw, add_comm, iterate_add_apply, h1, hv, T_iterate_eq_U hzo, iterate_succ_apply']
    · by_cases hjr : j ≤ wsum (vword N) r + r
      · obtain ⟨i, hi, hle⟩ := h2 j hjr
        exact ⟨i, by omega, hle⟩
      · push Not at hjr
        set k := j - (wsum (vword N) r + r) with hk
        have hj' : T^[j] N = T^[k] z := by
          rw [← h1, ← iterate_add_apply]; congr 1; omega
        have hk1 : 1 ≤ k := by omega
        have hk2 : k ≤ padicValNat 2 (3 * z + 1) + 1 := by rw [← hv]; omega
        refine ⟨r + 1, le_rfl, ?_⟩
        rw [hj', T_iterate_odd hzo k hk1 hk2, iterate_succ_apply', ← hz]
        unfold U
        exact Nat.div_le_div_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

/-- The shortcut orbit over `r` odd blocks: `F^{S_r}(N) = U^r(N)`, and every intermediate shortcut
state is at least some `U^i(N)`, `i ≤ r`. -/
lemma F_blocks {N : ℕ} (hN : Odd N) (r : ℕ) :
    F^[wsum (vword N) r] N = U^[r] N ∧
      ∀ j ≤ wsum (vword N) r, ∃ i ≤ r, U^[i] N ≤ F^[j] N := by
  induction r with
  | zero => exact ⟨by simp [wsum], fun j hj => ⟨0, le_rfl, by simp [wsum] at hj; subst hj; simp⟩⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    set z := U^[r] N with hz
    have hzo : Odd z := odd_U_iterate hN r
    have hv : vword N r = padicValNat 2 (3 * z + 1) := rfl
    have hw : wsum (vword N) (r + 1) = wsum (vword N) r + vword N r := by
      simp only [wsum, Finset.sum_range_succ]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hw, add_comm, iterate_add_apply, h1, hv, F_iterate_eq_U hzo, iterate_succ_apply']
    · by_cases hjr : j ≤ wsum (vword N) r
      · obtain ⟨i, hi, hle⟩ := h2 j hjr
        exact ⟨i, by omega, hle⟩
      · push Not at hjr
        set k := j - wsum (vword N) r with hk
        have hj' : F^[j] N = F^[k] z := by
          rw [← h1, ← iterate_add_apply]; congr 1; omega
        have hk1 : 1 ≤ k := by omega
        have hk2 : k ≤ padicValNat 2 (3 * z + 1) := by rw [← hv]; omega
        refine ⟨r + 1, le_rfl, ?_⟩
        rw [hj', F_iterate_odd hzo k hk1 hk2, iterate_succ_apply', ← hz]
        unfold U
        exact Nat.div_le_div_left (pow_le_pow_right₀ (by norm_num) hk2) (by positivity)

/-! ## The early segment stays above `x` -/

lemma lt_of_lt_passT {x : ℝ} {N i : ℕ} (hi : i < passT x N) : x < (U^[i] N : ℝ) := by
  by_contra h
  push Not at h
  exact (not_le.mpr hi) (Nat.sInf_le (show i ∈ {r : ℕ | (U^[r] N : ℝ) ≤ x} from h))

/-- Setting of the transport property: with `m ≥ 1`, the odd states `U^i(N)`, `i ≤ r`, of the
early segment all exceed `x`. -/
lemma early_above {x : ℝ} {N : ℕ} (hm1 : 1 ≤ mT x) (hmT : mT x ≤ passT x N) :
    ∀ i ≤ passT x N - mT x, x < (U^[i] N : ℝ) :=
  fun i hi => lt_of_lt_passT (by omega)

/-! ## The three clocks -/

theorem transport_T (b : ℕ) :
    Transport (Pred T b) (fun n => -(hit T b n : ℝ)) 1 1 (b + 1) := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  obtain ⟨hTb, hTst⟩ := T_blocks hN r
  have hab := early_above hm1 hmT
  have hav : ∀ j ≤ wsum (vword N) r + r, T^[j] N ≠ b := by
    intro j hj hjb
    obtain ⟨i, hi, hle⟩ := hTst j hj
    have h1 := hab i hi
    have h2 : (U^[i] N : ℝ) ≤ b := by rw [← hjb]; exact_mod_cast hle
    linarith
  obtain ⟨hiff, hhit⟩ := pred_shift hTb hav hN.pos (odd_U_iterate hN r).pos
  refine ⟨hiff, fun hNA => ?_⟩
  simp only [hhit hNA]; push_cast; ring

theorem transport_F (b : ℕ) :
    Transport (Pred F b) (fun n => -(hit F b n : ℝ)) 1 0 (b + 1) := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  obtain ⟨hFb, hFst⟩ := F_blocks hN r
  have hab := early_above hm1 hmT
  have hav : ∀ j ≤ wsum (vword N) r, F^[j] N ≠ b := by
    intro j hj hjb
    obtain ⟨i, hi, hle⟩ := hFst j hj
    have h1 := hab i hi
    have h2 : (U^[i] N : ℝ) ≤ b := by rw [← hjb]; exact_mod_cast hle
    linarith
  obtain ⟨hiff, hhit⟩ := pred_shift hFb hav hN.pos (odd_U_iterate hN r).pos
  refine ⟨hiff, fun hNA => ?_⟩
  simp only [hhit hNA]; push_cast; ring

theorem transport_U (b : ℕ) :
    Transport (PredU b) (fun n => -(hit U b n : ℝ)) 0 1 (b + 1) := by
  intro x hx hm1 N hN _ hmT _
  set r := passT x N - mT x
  have hab := early_above hm1 hmT
  have hav : ∀ j ≤ r, U^[j] N ≠ b := by
    intro j hj hjb
    have h1 := hab j hj
    rw [hjb] at h1
    linarith
  obtain ⟨hiff, hhit⟩ := pred_shift (G := U) (k := r) rfl hav hN.pos (odd_U_iterate hN r).pos
  have hset : ∀ n, Odd n → (n ∈ PredU b ↔ n ∈ Pred U b) := fun n hn =>
    ⟨fun ⟨h0, _, h⟩ => ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨h0, hn, h⟩⟩
  rw [hset N hN, hset _ (odd_U_iterate hN r)]
  refine ⟨hiff, fun hNA => ?_⟩
  simp only [hhit hNA]; push_cast; ring

end CollatzCLT
