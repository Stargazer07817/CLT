import LeanClt.Transfer.Typical
import LeanClt.Transfer.Asymp

/-!
# Lemma 5.1 (typical valuations)

`Good x N`: `|S_j(N) - 2j| ≤ L^{0.6}` for all `j ≤ n₀`. For every `A > 0`, for large `x` and
all `Y ≥ x^α`, `P(N_Y not good) ≤ L^{-A}`. Proved without the coupling import, through
`count_dev_le`.
-/

open Real Finset Filter Topology

namespace CollatzCLT

/-- The typical event `𝒢` of Lemma 5.1. -/
def Good (x : ℝ) (N : ℕ) : Prop := ∀ j ≤ n0 x, |(Swd N j : ℝ) - 2 * j| ≤ Lx x ^ (0.6 : ℝ)

lemma ell_lt_07 : ell < 0.7 := by have := ell_lt_one; unfold ell; have := Real.log_two_lt_d9; linarith

/-- `L_Y ≥ Y/2 - 3/2`. -/
lemma LY_ge {Y : ℝ} (hY : 0 ≤ Y) : Y / 2 - 3 / 2 ≤ (LY Y : ℝ) := by
  have h := LY_bound hY
  have h1 : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one hY
  have h2 : 2 * Y < (⌊2 * Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hle := oddClosed_bounds hY
  have h3 : ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) = (⌊2 * Y⌋₊ : ℝ) + 1 - ⌈Y⌉₊ := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [h3] at h
  have := (abs_le.mp h).1
  linarith

lemma chern_le_of {j : ℕ} {t k : ℝ} (hk : k ≤ min (t ^ 2 / (12 * j)) (t / 8)) :
    chern j t ≤ 2 * Real.exp (-k) := by
  unfold chern; gcongr

open Classical in
/-- **Lemma 5.1 (typical valuations).** -/
theorem typical (A : ℝ) : ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ alpha ≤ Y →
    (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) ≤ Lx x ^ (-A) * LY Y := by
  have hl := ell_pos; have hl7 := ell_lt_07
  have e1 := ev_pow_mul_exp_le 1 (A + 1) (k := 1 / 2) (b := 0.2) (by norm_num) (by norm_num)
  have e2 := ev_pow_mul_exp_le 1 (A + 1) (k := 1 / 84) (b := 1) (by norm_num) (by norm_num)
  have e3 := ev_pow_mul_exp_le 1 (A + 1) (k := 0.701) (b := 1) (by norm_num) (by norm_num)
  have e4 : ∀ᶠ L : ℝ in atTop, (4 : ℝ) ≤ L ^ (0.4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.4)).eventually (eventually_ge_atTop 4)
  filter_upwards [ev_of_log e1, ev_of_log e2, ev_of_log e3, ev_of_log e4,
    ev_of_log (eventually_ge_atTop (100 : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with x h1 h2 h3 h4 hL hx0 Y hY
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  set n := n0 x with hn
  have hn1 : (n : ℝ) ≤ L / (10 * ell) := n0_le x (by linarith)
  have hn2 : L / (10 * ell) - 1 ≤ (n : ℝ) := n0_ge x
  have hnL6 : (n : ℝ) ≤ L / 6 := hn1.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [ell_gt])
  have hnL7 : L / 7 - 1 ≤ (n : ℝ) := le_trans (by
    have : L / 7 ≤ L / (10 * ell) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith) hn2
  have hY0 : 0 ≤ Y := le_trans (Real.rpow_nonneg hx0.le _) hY
  set LYr := (LY Y : ℝ)
  have hLY : Real.exp (1.001 * L) / 4 ≤ LYr := by
    have hxa : x ^ alpha = Real.exp (1.001 * L) := by
      rw [rpow_eq_exp_Lx hx0, hLdef]; unfold alpha; norm_num
    have := LY_ge hY0
    have hbig : 6 ≤ Real.exp (1.001 * L) := by
      have := Real.add_one_le_exp (1.001 * L); linarith
    linarith
  have hLYpos : 0 < LYr := lt_of_lt_of_le (by positivity) hLY
  -- the union bound over `j ∈ [1, n]`
  have hsub : (oddClosed Y).filter (fun N => ¬ Good x N) ⊆
      (Icc 1 n).biUnion (fun j => (oddClosed Y).filter
        (fun N => L ^ (0.6 : ℝ) ≤ |(Swd N j : ℝ) - 2 * j|)) := by
    intro N hN
    simp only [Finset.mem_filter, Good, not_forall, not_le] at hN
    obtain ⟨hNo, j, hj, hdev⟩ := hN
    rw [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, hj⟩, Finset.mem_filter.mpr ⟨hNo, hdev.le⟩⟩
    by_contra h0
    push Not at h0
    have : j = 0 := by omega
    subst this
    have hS0 : Swd N 0 = 0 := by simp [Swd, wsum]
    rw [hS0] at hdev
    norm_num at hdev
    linarith [Real.rpow_nonneg hL0.le (0.6 : ℝ)]
  have hj_bound : ∀ j ∈ Icc 1 n, (((oddClosed Y).filter
      (fun N => L ^ (0.6 : ℝ) ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℝ) ≤
      LYr * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) + 2 * Real.exp (-(n / 12))) +
        2 ^ (3 * n + 3) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj.2
    have hdev := count_dev_le hY0 hj.1 (Real.rpow_nonneg hL0.le (0.6 : ℝ)) (K := 3 * n)
      (by omega)
    refine hdev.trans ?_
    have c1 : chern j (L ^ (0.6 : ℝ)) ≤ 2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) := by
      apply chern_le_of
      apply le_min
      · rw [le_div_iff₀ (by positivity)]
        have hp : (L ^ (0.6 : ℝ)) ^ 2 = L ^ (0.2 : ℝ) * L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, show (0.6 : ℝ) * (2 : ℕ) = 0.2 + 1 by
            norm_num, Real.rpow_add hL0, Real.rpow_one]
        rw [hp]
        have : 12 * (j : ℝ) ≤ 2 * L := by linarith
        have hp0 : 0 ≤ L ^ (0.2 : ℝ) := Real.rpow_nonneg hL0.le _
        nlinarith
      · have hp : L ^ (0.6 : ℝ) = L ^ (0.4 : ℝ) * L ^ (0.2 : ℝ) := by
          rw [← Real.rpow_add hL0]; norm_num
        rw [hp]
        have hp0 : 0 ≤ L ^ (0.2 : ℝ) := Real.rpow_nonneg hL0.le _
        nlinarith
    have c2 : chern j (((3 * n : ℕ) : ℝ) - 2 * j) ≤ 2 * Real.exp (-(n / 12)) := by
      apply chern_le_of
      have hx : (n : ℝ) ≤ ((3 * n : ℕ) : ℝ) - 2 * j := by push_cast; linarith
      apply le_min
      · rw [le_div_iff₀ (by positivity)]
        have hx0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        nlinarith
      · linarith
    have hLY0 : 0 ≤ LYr := hLYpos.le
    gcongr
  -- assemble
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) ≤
      n * (LYr * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) + 2 * Real.exp (-(n / 12))) +
        2 ^ (3 * n + 3)) := by
    calc _ ≤ ((∑ j ∈ Icc 1 n, ((oddClosed Y).filter
          (fun N => L ^ (0.6 : ℝ) ≤ |(Swd N j : ℝ) - 2 * j|)).card : ℕ) : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ∑ j ∈ Icc 1 n, (LYr * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) +
          2 * Real.exp (-(n / 12))) + 2 ^ (3 * n + 3)) := by
          push_cast; exact Finset.sum_le_sum hj_bound
      _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  -- the three error terms
  have hpow : (2 : ℝ) ^ (3 * n + 3) ≤ 8 * Real.exp (0.3 * L) := by
    have : (2 : ℝ) ^ (3 * n + 3) = 8 * Real.exp (3 * n * ell) := by
      rw [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm, ← Real.exp_log (by norm_num :
        (0 : ℝ) < 2), ← Real.exp_nat_mul]
      unfold ell; push_cast; ring_nf
    rw [this]
    have h' : (n : ℝ) * ell ≤ L / 10 := by
      have := mul_le_mul_of_nonneg_right hn1 hl.le
      rwa [show L / (10 * ell) * ell = L / 10 by field_simp] at this
    have h'' : 3 * (n : ℝ) * ell ≤ 0.3 * L := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h'') (by norm_num)
  have hLA : L ^ (-(A + 1)) * 96 ≤ L ^ (-A) := by
    have e : L ^ (-A) = L ^ (-(A + 1)) * L := by
      rw [← Real.rpow_add_one hL0.ne']; ring_nf
    rw [e]; gcongr; linarith
  have hLApos : 0 ≤ L ^ (-(A + 1)) := Real.rpow_nonneg hL0.le _
  have t1 : (n : ℝ) * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) ≤ 2 * L ^ (-(A + 1)) := by
    have : (n : ℝ) ≤ L := by linarith
    have h1' : L ^ (1 : ℝ) * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) ≤ L ^ (-(A + 1)) := h1
    simp only [Real.rpow_one] at h1'
    have he := Real.exp_pos (-(1 / 2 * L ^ (0.2 : ℝ)))
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (n : ℝ) * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))))
        ≤ L * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) := by gcongr
      _ = 2 * (L * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) := by ring
      _ ≤ 2 * L ^ (-(A + 1)) := by gcongr
  have t2 : (n : ℝ) * (2 * Real.exp (-(n / 12))) ≤ 6 * L ^ (-(A + 1)) := by
    have h2' : L ^ (1 : ℝ) * Real.exp (-(1 / 84 * L ^ (1 : ℝ))) ≤ L ^ (-(A + 1)) := h2
    simp only [Real.rpow_one] at h2'
    have hle : Real.exp (-(n / 12)) ≤ 3 * Real.exp (-(1 / 84 * L)) := by
      have : -(n / 12 : ℝ) ≤ 1 + -(1 / 84 * L) := by linarith
      calc Real.exp (-(n / 12)) ≤ Real.exp (1 + -(1 / 84 * L)) := Real.exp_le_exp.mpr this
        _ = Real.exp 1 * Real.exp (-(1 / 84 * L)) := Real.exp_add _ _
        _ ≤ 3 * Real.exp (-(1 / 84 * L)) := by
            gcongr; have := Real.exp_one_lt_d9; linarith
    have : (n : ℝ) ≤ L := by linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he := Real.exp_pos (-(1 / 84 * L))
    calc (n : ℝ) * (2 * Real.exp (-(n / 12))) ≤ L * (2 * (3 * Real.exp (-(1 / 84 * L)))) := by
          gcongr
      _ = 6 * (L * Real.exp (-(1 / 84 * L))) := by ring
      _ ≤ 6 * L ^ (-(A + 1)) := by gcongr
  have t3 : (n : ℝ) * 2 ^ (3 * n + 3) ≤ 32 * L ^ (-(A + 1)) * LYr := by
    have h3' : L ^ (1 : ℝ) * Real.exp (-(0.701 * L ^ (1 : ℝ))) ≤ L ^ (-(A + 1)) := h3
    simp only [Real.rpow_one] at h3'
    have : (n : ℝ) ≤ L := by linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hsplit : Real.exp (0.3 * L) = Real.exp (-(0.701 * L)) * Real.exp (1.001 * L) := by
      rw [← Real.exp_add]; ring_nf
    calc (n : ℝ) * 2 ^ (3 * n + 3) ≤ L * (8 * Real.exp (0.3 * L)) := by gcongr
      _ = 32 * (L * Real.exp (-(0.701 * L))) * (Real.exp (1.001 * L) / 4) := by
          rw [hsplit]; ring
      _ ≤ 32 * L ^ (-(A + 1)) * LYr := by gcongr
  calc _ ≤ n * (LYr * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) + 2 * Real.exp (-(n / 12))) +
        2 ^ (3 * n + 3)) := hsum
    _ = LYr * ((n : ℝ) * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) +
        (n : ℝ) * (2 * Real.exp (-(n / 12)))) + (n : ℝ) * 2 ^ (3 * n + 3) := by ring
    _ ≤ LYr * (2 * L ^ (-(A + 1)) + 6 * L ^ (-(A + 1))) + 32 * L ^ (-(A + 1)) * LYr := by
        gcongr
    _ = (L ^ (-(A + 1)) * 40) * LYr := by ring
    _ ≤ L ^ (-A) * LYr := by gcongr; linarith

end CollatzCLT
