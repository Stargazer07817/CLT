import LeanClt.Transfer.Orbit

/-!
# The "large `x`" conditions of §5, collected

`Large x` packages the finitely many numerical inequalities between `L = log x`, `m` and `n₀`
used in Lemmas 5.2 and 5.4 (and later). `large_ev`: they all hold for large `x`.

Also: the depth window `J_Y` (5.4, `eq:JY`) and its centre `r_Y`.
-/

open Real Finset Filter Topology

namespace CollatzCLT

/-- `r_Y = log(Y/x)/c - m`. -/
noncomputable def rY (x Y : ℝ) : ℝ := Real.log (Y / x) / c - mT x

/-- The depth window `J_Y = {r : |r - r_Y| ≤ 2L^{0.8}}` (intersected with `[0, n₀]`). -/
noncomputable def JY (x Y : ℝ) : Finset ℕ :=
  (range (n0 x + 1)).filter (fun r => |(r : ℝ) - rY x Y| ≤ 2 * Lx x ^ (0.8 : ℝ))

lemma c_ge_quarter : (1 / 4 : ℝ) ≤ c := by
  unfold c
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  norm_num at this ⊢; linarith

/-- The numerical conditions on `L`, `m`, `n₀` used in §5. -/
structure Large (x : ℝ) : Prop where
  x_gt : 1 < x
  L_ge : 200000 ≤ Lx x
  m_ge : 1 ≤ mT x
  cross : alpha ^ 2 * Lx x + ell + 1 - c * n0 x + ell * Lx x ^ (0.6 : ℝ) < Lx x
  hwin : (ell * Lx x ^ (0.6 : ℝ) + 1 + c + ell) / c ≤ 2 * Lx x ^ (0.8 : ℝ)
  mwin : 2 * ell * Lx x ^ (0.6 : ℝ) + c + 2 ≤ Lx x ^ (0.7 : ℝ)
  conv : Lx x ^ (0.7 : ℝ) + 2 * ell * Lx x ^ (0.6 : ℝ) + 1 < c * mT x
  jlow : (alpha - 1) * Lx x / c - mT x - 2 * Lx x ^ (0.8 : ℝ) ≥ mT x
  jhigh : (alpha ^ 2 - 1) * Lx x / c - mT x + 2 * Lx x ^ (0.8 : ℝ) ≤ n0 x - mT x
  err : ell * (n0 x + Lx x ^ (0.6 : ℝ)) ≤ alpha * Lx x
  harm : bet * n0 x + mT x * Real.log (1 + √2) ≤ Lx x / 4

lemma alpha_val : alpha = 1.001 := rfl

/-- `o(L)` facts used below: `L^a ≤ ε L` for `a < 1`, eventually. -/
lemma ev_rpow_le_mul {a ε : ℝ} (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, L ^ a ≤ ε * L := by
  have h := ev_pow_mul_exp_le (a := 0) (A := 0) (k := 1) (b := 1) (by norm_num) (by norm_num)
  -- `L^{a-1} → 0`
  have ht : Tendsto (fun L : ℝ => L ^ (a - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (show 0 < 1 - a by linarith)
    simpa [neg_sub] using this
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have e : L ^ a = L ^ (a - 1) * L := by rw [← Real.rpow_add_one hL0.ne']; ring_nf
  rw [e]; gcongr

/-- `L^a ≤ ε L^b` for `a < b`, eventually. -/
lemma ev_rpow_le_rpow {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, L ^ a ≤ ε * L ^ b := by
  have ht : Tendsto (fun L : ℝ => L ^ (a - b)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (show 0 < b - a by linarith)
    simpa [neg_sub] using this
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have e : L ^ a = L ^ (a - b) * L ^ b := by rw [← Real.rpow_add hL0]; ring_nf
  rw [e]; gcongr

-- many independent numerical side conditions are checked in one proof
set_option maxHeartbeats 1000000 in
/-- **All the conditions hold for large `x`.** -/
theorem large_ev : ∀ᶠ x : ℝ in atTop, Large x := by
  have hc := c_pos'; have hc3 := c_lt_third; have hc4 := c_ge_quarter
  have hl := ell_pos; have hl7 := ell_lt_07; have hl6 := ell_gt
  have e1 := ev_rpow_le_mul (a := 0.6) (ε := 0.001) (by norm_num) (by norm_num)
  have e2 := ev_rpow_le_rpow (a := 0.6) (b := 0.8) (ε := 0.1) (by norm_num) (by norm_num)
  have e3 := ev_rpow_le_rpow (a := 0.6) (b := 0.7) (ε := 0.1) (by norm_num) (by norm_num)
  have e4 := ev_rpow_le_mul (a := 0.7) (ε := 10 ^ (-7 : ℤ)) (by norm_num) (by norm_num)
  have e5 := ev_rpow_le_mul (a := 0.8) (ε := 10 ^ (-5 : ℤ)) (by norm_num) (by norm_num)
  have e6 : ∀ᶠ L : ℝ in atTop, (100 : ℝ) ≤ L ^ (0.6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.6)).eventually (eventually_ge_atTop 100)
  filter_upwards [ev_of_log e1, ev_of_log e2, ev_of_log e3, ev_of_log e4, ev_of_log e5,
    ev_of_log e6, ev_of_log (eventually_ge_atTop (10 ^ 9 : ℝ)), eventually_gt_atTop (1 : ℝ)]
    with x h1 h2 h3 h4 h5 h6 hL hx1
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  have hm1 := mT_le x (by linarith)
  have hm2 := mT_ge x
  have hn1 := n0_le x (by linarith)
  have hn2 := n0_ge x
  simp only [← hLdef, alpha_val] at hm1 hm2 hn1 hn2
  have h06 : 0 ≤ L ^ (0.6 : ℝ) := Real.rpow_nonneg hL0.le _
  have h07 : 0 ≤ L ^ (0.7 : ℝ) := Real.rpow_nonneg hL0.le _
  have h08 : 0 ≤ L ^ (0.8 : ℝ) := Real.rpow_nonneg hL0.le _
  -- `n₀ ≥ L/7 - 1`, `n₀ ≤ L/6`
  have hn7 : L / 7 - 1 ≤ (n0 x : ℝ) := le_trans (by
    have : L / 7 ≤ L / (10 * ell) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith) hn2
  have hnell : ell * (n0 x : ℝ) ≤ L / 10 := by
    have := mul_le_mul_of_nonneg_left hn1 hl.le
    rwa [show ell * (L / (10 * ell)) = L / 10 by field_simp] at this
  have hcm : c * (mT x : ℝ) ≥ c * (0.001 * L / 100 - 1) := by
    apply mul_le_mul_of_nonneg_left _ hc.le; norm_num at hm2 ⊢; linarith
  refine ⟨hx1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [alpha_val, ← hLdef]
  · linarith
  · have : (1 : ℝ) ≤ mT x := by norm_num at hm2; linarith
    exact_mod_cast this
  · -- crossing before `n₀`
    have hcn : c * (n0 x : ℝ) ≥ c * (L / 7 - 1) := mul_le_mul_of_nonneg_left hn7 hc.le
    nlinarith
  · rw [div_le_iff₀ hc]
    nlinarith
  · nlinarith
  · nlinarith
  · -- the window lies above `m`
    have : (0.001 : ℝ) * L / c ≥ 0.003 * L := by
      rw [ge_iff_le, le_div_iff₀ hc]; nlinarith
    norm_num at hm1 h5 ⊢
    nlinarith
  · -- the window lies below `n₀ - m`
    have : ((1.001 : ℝ) ^ 2 - 1) * L / c ≤ 0.009 * L := by
      rw [div_le_iff₀ hc]; nlinarith
    norm_num at hm1 h5 this ⊢
    nlinarith
  · have : ell * L ^ (0.6 : ℝ) ≤ 0.7 * L ^ (0.6 : ℝ) := mul_le_mul_of_nonneg_right hl7.le h06
    rw [mul_add]
    linarith
  · -- `β n₀ + m log(1+√2) ≤ L/4`
    have hb : bet ≤ 1.15 := by have h := c_eq; linarith only [h, hc4, hl7]
    have hb0 : 0 < bet := bet_pos
    have hlog : Real.log (1 + √2) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      have h2 : √2 ≤ 1.5 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have := Real.exp_one_gt_d9
      linarith
    have hn6 : (n0 x : ℝ) ≤ L / 6.9 := hn1.trans (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have hm0 : (0 : ℝ) ≤ mT x := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ n0 x := Nat.cast_nonneg _
    have h1' : bet * (n0 x : ℝ) ≤ 1.15 * (L / 6.9) := by
      apply mul_le_mul hb hn6 hn0 (by norm_num)
    have h2' : (mT x : ℝ) * Real.log (1 + √2) ≤ (mT x : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog hm0
    have hm1' : (mT x : ℝ) ≤ L / 100000 := by norm_num at hm1 ⊢; linarith only [hm1]
    have e1 : (1.15 : ℝ) * (L / 6.9) ≤ 0.17 * L := by
      rw [show (1.15 : ℝ) * (L / 6.9) = (1.15 / 6.9) * L by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) hL0.le
    have e2 : L / 100000 ≤ 0.01 * L := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    have e3 : (0.17 : ℝ) * L + 0.01 * L ≤ L / 4 := by linarith
    linarith only [h1', h2', hm1', e1, e2, e3]

end CollatzCLT
