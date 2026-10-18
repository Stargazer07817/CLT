import LeanClt.Transfer.Geom

/-!
# Auxiliary bounds for Proposition 5.5

* `sum_inv_spaced_le`: if the elements of a finite set `T ⊆ [K₀, K₁]` (`K₀ > 0`) are pairwise at
  least `Q` apart, then `∑_{t ∈ T} 1/t ≤ 1/K₀ + log(K₁/K₀)/Q`.
* `sum_words_last_le`: `∑_{S ≤ K} ∑_{b ∈ words (n+1) S} b_n 2^{-S} ≤ 2` (`E[a_{n+1}] = 2`).
* `sum_words_sqrt_le`: `∑_{S ≤ K} ∑_{b ∈ words n S} 2^{-S/2} ≤ (1+√2)^n`.
-/

open Real Finset

namespace CollatzCLT

/-- `1/t ≤ log(t/t')/Q` when `t ≥ t' + Q`, `t' > 0`. -/
lemma inv_le_log_div {t t' Q : ℝ} (ht' : 0 < t') (hQ : 0 < Q) (h : t' + Q ≤ t) :
    1 / t ≤ Real.log (t / t') / Q := by
  have ht : 0 < t := by linarith
  rw [div_le_div_iff₀ ht hQ, one_mul]
  -- `log(t/t') ≥ 1 - t'/t ≥ Q/t`
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < t / t' by positivity)
  rw [inv_div] at h1
  have h2 : Q / t ≤ 1 - t' / t := by
    rw [div_le_iff₀ ht, sub_mul, div_mul_cancel₀ _ ht.ne']; linarith
  have h3 : Q ≤ Real.log (t / t') * t := by
    have := (div_le_iff₀ ht).mp (h2.trans h1)
    linarith
  linarith

/-- **Reciprocal sum over a `Q`-spaced set.** -/
theorem sum_inv_spaced_le {Q K₀ K₁ : ℝ} (hQ : 0 < Q) (hK₀ : 0 < K₀) (hK : K₀ ≤ K₁) :
    ∀ T : Finset ℕ, (∀ t ∈ T, K₀ ≤ t ∧ (t : ℝ) ≤ K₁) →
      (∀ t ∈ T, ∀ t' ∈ T, t' < t → (t' : ℝ) + Q ≤ t) →
        ∑ t ∈ T, (1 : ℝ) / t ≤ 1 / K₀ + Real.log (K₁ / K₀) / Q := by
  have hlog0 : 0 ≤ Real.log (K₁ / K₀) / Q :=
    div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hK₀]; linarith)) hQ.le
  -- strengthen: the bound with `K₁` replaced by the maximum of `T`
  suffices key : ∀ T : Finset ℕ, ∀ hne : T.Nonempty, (∀ t ∈ T, K₀ ≤ t) →
      (∀ t ∈ T, ∀ t' ∈ T, t' < t → (t' : ℝ) + Q ≤ t) →
        ∑ t ∈ T, (1 : ℝ) / t ≤ 1 / K₀ + Real.log ((T.max' hne : ℝ) / K₀) / Q by
    intro T hT hsp
    rcases T.eq_empty_or_nonempty with rfl | hne
    · simp; positivity
    refine (key T hne (fun t ht => (hT t ht).1) hsp).trans ?_
    gcongr
    · exact div_pos (lt_of_lt_of_le hK₀ (hT _ (T.max'_mem hne)).1) hK₀
    · exact (hT _ (T.max'_mem hne)).2
  intro T
  refine Finset.induction_on_max T ?_ ?_
  · intro h; exact absurd h Finset.not_nonempty_empty
  · intro a s hlt ih hne' hK hsp
    have ha : K₀ ≤ a := hK a (Finset.mem_insert_self a s)
    have ha0 : (0 : ℝ) < a := lt_of_lt_of_le hK₀ ha
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.sum_insert has]
    have hmax : (insert a s).max' ‹_› = a := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (fun y hy => by
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact (hlt y hy).le)
      · exact Finset.le_max' _ _ (Finset.mem_insert_self a s)
    rw [hmax]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp only [Finset.sum_empty, add_zero]
      have : 1 / (a : ℝ) ≤ 1 / K₀ := one_div_le_one_div_of_le hK₀ ha
      have : 0 ≤ Real.log ((a : ℝ) / K₀) / Q :=
        div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hK₀]; linarith)) hQ.le
      linarith
    · set b := s.max' hs
      have hbs : b ∈ s := s.max'_mem hs
      have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hK₀ (hK b (Finset.mem_insert_of_mem hbs))
      have hih := ih hs (fun t ht => hK t (Finset.mem_insert_of_mem ht))
        (fun t ht t' ht' h => hsp t (Finset.mem_insert_of_mem ht) t' (Finset.mem_insert_of_mem ht') h)
      have hgap : (b : ℝ) + Q ≤ a := hsp a (Finset.mem_insert_self a s) b
        (Finset.mem_insert_of_mem hbs) (hlt b hbs)
      have hstep := inv_le_log_div hb0 hQ hgap
      have hsplit : Real.log ((a : ℝ) / K₀) = Real.log ((a : ℝ) / b) + Real.log ((b : ℝ) / K₀) := by
        rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
      rw [hsplit, add_div]
      linarith

/-! ## Two sums over words -/

/-- `∑_{a=1}^{K} a 2^{-a} ≤ 2`. -/
lemma sum_mul_half_pow_le (K : ℕ) : ∑ a ∈ range (K + 1), (a : ℝ) * (1 / 2) ^ a ≤ 2 := by
  have hs : Summable (fun a : ℕ => (a : ℝ) * (1 / 2) ^ a) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    simpa using this
  have h := hs.sum_le_tsum (range (K + 1)) (fun i _ => by positivity)
  have ht : ∑' a : ℕ, (a : ℝ) * (1 / 2) ^ a = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num)]; norm_num
  linarith

/-- **`E[a_{n+1}] = 2`**, as a bound on partial sums. -/
theorem sum_words_last_le (n K : ℕ) :
    ∑ S ∈ range (K + 1), ∑ b ∈ words (n + 1) S, (b (Fin.last n) : ℝ) * (1 / 2) ^ S ≤ 2 := by
  -- split off the last letter
  have hsplit : ∀ S, ∑ b ∈ words (n + 1) S, (b (Fin.last n) : ℝ) * (1 / 2) ^ S =
      ∑ S1 ∈ range (S + 1), lawS n S1 * (if 1 ≤ S - S1 then ((S - S1 : ℕ) : ℝ) * (1 / 2) ^ (S - S1)
        else 0) := by
    intro S
    rw [sum_words_append n 1 S]
    refine Finset.sum_congr rfl fun S1 hS1 => ?_
    rw [words_one, ← sum_words_half, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with h
    · rw [Finset.sum_singleton]
      have : Fin.last n = Fin.natAdd n (0 : Fin 1) := rfl
      rw [this, Fin.append_right]
      rw [mem_range] at hS1
      rw [show S = S1 + (S - S1) by omega, pow_add]; ring_nf
      congr 1; congr 1; omega
    · simp
  simp_rw [hsplit]
  -- reorganise as a convolution and bound by `(∑ lawS) · 2`
  calc ∑ S ∈ range (K + 1), ∑ S1 ∈ range (S + 1), lawS n S1 *
        (if 1 ≤ S - S1 then ((S - S1 : ℕ) : ℝ) * (1 / 2) ^ (S - S1) else 0)
      ≤ ∑ S ∈ range (K + 1), ∑ S1 ∈ range (S + 1), lawS n S1 *
        (((S - S1 : ℕ) : ℝ) * (1 / 2) ^ (S - S1)) := by
        gcongr with S _ S1 _
        · exact lawS_nonneg _ _
        · split_ifs
          · exact le_rfl
          · positivity
    _ = ∑ S1 ∈ range (K + 1), lawS n S1 *
        ∑ a ∈ range (K + 1 - S1), (a : ℝ) * (1 / 2) ^ a := by
        rw [Finset.sum_range_diag_flip (K + 1)
          (fun k j => lawS n k * ((j : ℝ) * (1 / 2) ^ j))]
        refine Finset.sum_congr rfl fun S1 _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ S1 ∈ range (K + 1), lawS n S1 * 2 := by
        gcongr with S1 _
        · exact lawS_nonneg _ _
        · obtain ⟨k, hk⟩ : ∃ k, K + 1 - S1 = k + 1 ∨ K + 1 - S1 = 0 := ⟨K - S1, by omega⟩
          rcases hk with hk | hk
          · rw [hk]; exact sum_mul_half_pow_le k
          · rw [hk]; simp
    _ ≤ 1 * 2 := by
        rw [← Finset.sum_mul]
        gcongr
        have := (summable_lawS n).sum_le_tsum (range (K + 1)) (fun i _ => lawS_nonneg n i)
        rwa [tsum_lawS] at this
    _ = 2 := by norm_num

lemma sum_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ a ∈ range N, r ^ a ≤ 1 / (1 - r) := by
  have := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (range N) (fun i _ => by positivity)
  rwa [tsum_geometric_of_lt_one hr0 hr1, ← one_div] at this

lemma sum_geom_pos_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ a ∈ range N, (if 1 ≤ a then r ^ a else 0) ≤ r / (1 - r) := by
  rcases N with _ | k
  · simp; exact div_nonneg hr0 (by linarith)
  · rw [Finset.sum_range_succ']
    simp only [Nat.le_add_left, ↓reduceIte, pow_succ]
    rw [if_neg (by norm_num), add_zero, ← Finset.sum_mul, mul_comm, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (sum_geom_le hr0 hr1 k) hr0

/-- `∑_{S ≤ K} ∑_{b ∈ words n S} r^S ≤ (r/(1-r))^n`. -/
theorem sum_words_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∀ n : ℕ, ∑ S ∈ range (K + 1), ∑ b ∈ words n S, r ^ S ≤ (r / (1 - r)) ^ n := by
  have hq : 0 ≤ r / (1 - r) := div_nonneg hr0 (by linarith)
  intro n
  induction n with
  | zero =>
    simp only [pow_zero]
    rw [Finset.sum_eq_single 0]
    · simp [words_zero]
    · intro S _ hS; simp [words_zero, hS]
    · intro h; simp at h
  | succ n ih =>
    have hsplit : ∀ S, ∑ b ∈ words (n + 1) S, r ^ S = ∑ S1 ∈ range (S + 1),
        (∑ u ∈ words n S1, r ^ S1) * (if 1 ≤ S - S1 then r ^ (S - S1) else 0) := by
      intro S
      rw [sum_words_append n 1 S]
      refine Finset.sum_congr rfl fun S1 hS1 => ?_
      rw [mem_range] at hS1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [words_one]
      split_ifs with h
      · rw [Finset.sum_singleton, ← pow_add]; congr 1; omega
      · simp
    simp_rw [hsplit]
    rw [Finset.sum_range_diag_flip (K + 1) (fun k j => (∑ u ∈ words n k, r ^ k) *
      (if 1 ≤ j then r ^ j else 0))]
    calc ∑ S1 ∈ range (K + 1), ∑ a ∈ range (K + 1 - S1),
          (∑ u ∈ words n S1, r ^ S1) * (if 1 ≤ a then r ^ a else 0)
        = ∑ S1 ∈ range (K + 1), (∑ u ∈ words n S1, r ^ S1) *
          ∑ a ∈ range (K + 1 - S1), (if 1 ≤ a then r ^ a else 0) := by
          refine Finset.sum_congr rfl fun S1 _ => ?_; rw [Finset.mul_sum]
      _ ≤ ∑ S1 ∈ range (K + 1), (∑ u ∈ words n S1, r ^ S1) * (r / (1 - r)) := by
          gcongr with S1 _
          exact sum_geom_pos_le hr0 hr1 _
      _ = (∑ S1 ∈ range (K + 1), ∑ u ∈ words n S1, r ^ S1) * (r / (1 - r)) := by
          rw [Finset.sum_mul]
      _ ≤ (r / (1 - r)) ^ n * (r / (1 - r)) := by gcongr
      _ = (r / (1 - r)) ^ (n + 1) := by rw [pow_succ]

end CollatzCLT
