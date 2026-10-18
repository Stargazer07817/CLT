import LeanClt.Transfer.Large

/-!
# Lemma 5.3 (failure to cross) [`lem:failure`]

Stage 7 of the checkpoint-11 plan. The lemma has no consumer in the Lean tree: the proof of
Theorem 1.3 (i) [`thm:thresholds`] uses `AK_base` (Lemmas 5.1 and 5.2) at its base instead, because
only a `(log K)^{-δ}` bound is needed there (checkpoint 11, P3). It is formalized so that no label of
v8 is left without a Lean counterpart.

The proof is the paper's (§5.2):

* `U_n0_le_of_Swd`: on the event `S_{n₀} ≥ 1.9 n₀`, the affine formula (2.1, `eq:affine`) gives
  `U^{n₀}(N) ≤ x` for every odd `N ≤ 2x^{α²}`. The main term `3^{n₀} 2^{-S_{n₀}} N` is at most
  `x/2` because `β - 1.9ℓ < 0` (the paper's exponent `α² + (β - 1.9ℓ)/(10ℓ) = 0.9704… < 1`); this
  needs the lower bound `n₀ ≥ L/(10ℓ) - 1`, since the coefficient of `n₀` is negative. The offset
  is below `(3/2)^{n₀} ≤ x/2`.
* The complementary event is a linear deviation `|S_{n₀} - 2n₀| ≥ n₀/10`. The paper bounds it with
  Lemma 2.2 (i) [`lem:chernoff`] and the coupling of Lemma 5.1 [`lem:typical`]; in Lean both are
  `count_dev_le` at `j = n₀`, `t = n₀/10`, `K = 3n₀`, which gives
  `L_Y (4 e^{-n₀/1200}) + 2^{3n₀+3}` (the coupling import is not used, as in Lemma 5.1).

With `n₀ ≥ L/7 - 1` this is at most `40 x^{-1/8400} L_Y`, so `d₀ = 1/8400` and the implied
constant is `40`.
-/

open Real Finset Filter Topology

namespace CollatzCLT

/-- **The deterministic step of Lemma 5.3.** For `L = log x ≥ 200`, an odd `N ≤ 2x^{α²}` with
`S_{n₀}(N) ≥ 1.9 n₀` has `U^{n₀}(N) ≤ x`. -/
lemma U_n0_le_of_Swd {x : ℝ} (hx : 0 < x) (hL : 200 ≤ Lx x) {N : ℕ} (hN : Odd N)
    (hNY : (N : ℝ) ≤ 2 * x ^ (alpha ^ 2)) (hS : 1.9 * (n0 x : ℝ) ≤ Swd N (n0 x)) :
    (U^[n0 x] N : ℝ) ≤ x := by
  have hl := ell_pos; have hl7 := ell_lt_07; have hl6 := ell_gt
  have hc3 := c_lt_third; have hc4 := c_ge_quarter; have hce := c_eq
  set L := Lx x with hLdef
  set n := n0 x with hn
  set S := Swd N n with hSdef
  have hn1 : (n : ℝ) ≤ L / (10 * ell) := n0_le x (by linarith)
  have hn2 : L / (10 * ell) - 1 ≤ (n : ℝ) := n0_ge x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnL6 : (n : ℝ) ≤ L / 6 := hn1.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hnL7 : L / 7 - 1 ≤ (n : ℝ) := le_trans (by
    have : L / 7 ≤ L / (10 * ell) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith) hn2
  have hxL : x = Real.exp L := by rw [hLdef, Lx, Real.exp_log hx]
  have hbet : bet ≤ 1.15 := by linarith
  have hbet' : 1.04 ≤ bet := by linarith
  -- the affine formula (2.1) in `ℝ`, with `0 ≤ F ≤ (3/2)^n`
  have hU : (U^[n] N : ℝ) = 3 ^ n / 2 ^ S * N + ((offset (vword N) n : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (U_iterate_affine N n)
    push_cast at this
    exact this
  have hF : ((offset (vword N) n : ℚ) : ℝ) ≤ (3 / 2 : ℝ) ^ n := by
    have h1 := offset_le (vword N) (fun i => vword_pos hN i) n
    have : ((offset (vword N) n : ℚ) : ℝ) ≤ (((3 / 2 : ℚ) ^ n - 1 : ℚ) : ℝ) := by
      exact_mod_cast h1
    push_cast at this; linarith
  -- powers as exponentials
  have h3 : (3 : ℝ) ^ n = Real.exp (n * bet) := by
    rw [Real.exp_nat_mul, bet, Real.exp_log (by norm_num)]
  have h2 : (2 : ℝ) ^ S = Real.exp (S * ell) := by
    rw [Real.exp_nat_mul, exp_ell]
  have h32 : (3 / 2 : ℝ) ^ n = Real.exp (n * (bet - ell)) := by
    rw [Real.exp_nat_mul, show bet - ell = Real.log (3 / 2) by
      unfold bet ell; rw [Real.log_div (by norm_num) (by norm_num)], Real.exp_log (by norm_num)]
  have hxa : x ^ (alpha ^ 2) = Real.exp (alpha ^ 2 * L) := rpow_eq_exp_Lx hx _
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith
  -- the main term is at most `x/2`, because `β - 1.9ℓ < 0`
  have hmain : 3 ^ n / 2 ^ S * (N : ℝ) ≤ x / 2 := by
    have hexp : n * bet - S * ell + alpha ^ 2 * L ≤ L - 2 := by
      have hS' : 1.9 * (n : ℝ) * ell ≤ S * ell := mul_le_mul_of_nonneg_right hS hl.le
      have ha2 : alpha ^ 2 = 1.002001 := by unfold alpha; norm_num
      rw [ha2]
      have hk : (n : ℝ) * (bet - 1.9 * ell) ≤ (L / 7 - 1) * (bet - 1.9 * ell) :=
        mul_le_mul_of_nonpos_right hnL7 (by linarith)
      have hk2 : L * (bet - 1.9 * ell) ≤ L * (-0.161) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    calc 3 ^ n / 2 ^ S * (N : ℝ) ≤ 3 ^ n / 2 ^ S * (2 * x ^ (alpha ^ 2)) := by gcongr
      _ = 2 * Real.exp (n * bet - S * ell + alpha ^ 2 * L) := by
          rw [h3, h2, hxa, Real.exp_add, Real.exp_sub]; ring
      _ ≤ 2 * Real.exp (L - 2) := by gcongr
      _ = 2 * (Real.exp L / Real.exp 2) := by rw [Real.exp_sub]
      _ ≤ 2 * (Real.exp L / 4) := by gcongr
      _ = x / 2 := by rw [hxL]; ring
  -- the offset is at most `x/2`
  have hoff : (3 / 2 : ℝ) ^ n ≤ x / 2 := by
    have hk : (n : ℝ) * (bet - ell) ≤ L - 1 := by
      have : (n : ℝ) * (bet - ell) ≤ (L / 6) * (bet - ell) :=
        mul_le_mul_of_nonneg_right hnL6 (by linarith)
      have hk2 : L * (bet - ell) ≤ L * 0.46 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    calc (3 / 2 : ℝ) ^ n = Real.exp (n * (bet - ell)) := h32
      _ ≤ Real.exp (L - 1) := Real.exp_le_exp.mpr hk
      _ = Real.exp L / Real.exp 1 := Real.exp_sub _ _
      _ ≤ Real.exp L / 2 := by gcongr
      _ = x / 2 := by rw [hxL]
  rw [hU]
  linarith

open Classical in
/-- **Lemma 5.3 (failure to cross) [`lem:failure`].** `P(T_x(N_Y) = ∞) ≪ x^{-d₀}` uniformly in
`x^α ≤ Y ≤ x^{α²}`, written as a count over the odd integers of `[Y, 2Y]`; the proof gives
`d₀ = 1/8400` and implied constant `40`. -/
theorem failure_to_cross : ∃ d0 C : ℝ, 0 < d0 ∧ ∀ᶠ x : ℝ in atTop, ∀ Y : ℝ, x ^ alpha ≤ Y →
    Y ≤ x ^ (alpha ^ 2) →
      (((oddClosed Y).filter (fun N => ¬ crosses x N)).card : ℝ) ≤ C * x ^ (-d0) * LY Y := by
  refine ⟨1 / 8400, 40, by norm_num, ?_⟩
  have hl := ell_pos; have hl7 := ell_lt_07; have hl6 := ell_gt
  filter_upwards [ev_of_log (eventually_ge_atTop (200 : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with x hL hx0 Y hY hY2
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  set n := n0 x with hn
  have hn1 : (n : ℝ) ≤ L / (10 * ell) := n0_le x (by linarith)
  have hn2 : L / (10 * ell) - 1 ≤ (n : ℝ) := n0_ge x
  have hnL7 : L / 7 - 1 ≤ (n : ℝ) := le_trans (by
    have : L / 7 ≤ L / (10 * ell) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith) hn2
  have hn1' : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1'
  have hY0 : 0 ≤ Y := le_trans (Real.rpow_nonneg hx0.le _) hY
  set LYr := (LY Y : ℝ) with hLYr
  have hLY0 : 0 ≤ LYr := Nat.cast_nonneg _
  have hLY : Real.exp (1.001 * L) / 4 ≤ LYr := by
    have hxa : x ^ alpha = Real.exp (1.001 * L) := by
      rw [rpow_eq_exp_Lx hx0, hLdef]; unfold alpha; norm_num
    have := LY_ge hY0
    have hbig : 6 ≤ Real.exp (1.001 * L) := by
      have := Real.add_one_le_exp (1.001 * L); linarith
    linarith
  -- a source that fails to cross has a linear deviation of `S_{n₀}`
  have hsub : (oddClosed Y).filter (fun N => ¬ crosses x N) ⊆
      (oddClosed Y).filter (fun N => (n : ℝ) / 10 ≤ |(Swd N n : ℝ) - 2 * n|) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    refine ⟨hN.1, ?_⟩
    by_contra hdev
    apply hN.2
    have hmem := hN.1
    unfold oddClosed at hmem
    rw [Finset.mem_filter, Finset.mem_Icc] at hmem
    have hN2 : (N : ℝ) ≤ 2 * x ^ (alpha ^ 2) := by
      have h2 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
      have h1' : (N : ℝ) ≤ ⌊2 * Y⌋₊ := by exact_mod_cast hmem.1.2
      linarith
    have hS : 1.9 * (n : ℝ) ≤ Swd N n := by
      have := (abs_lt.mp (not_le.mp hdev)).1; linarith
    exact ⟨n, U_n0_le_of_Swd hx0 hL hmem.2 hN2 hS⟩
  -- the deviation count (Lemma 2.2 (i) with the comparison to the geometric model)
  have hdev := count_dev_le hY0 hn1' (t := (n : ℝ) / 10) (by positivity) (K := 3 * n) (by omega)
  have c1 : chern n ((n : ℝ) / 10) ≤ 2 * Real.exp (-((n : ℝ) / 1200)) := by
    apply chern_le_of
    apply le_min
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · linarith
  have c2 : chern n (((3 * n : ℕ) : ℝ) - 2 * n) ≤ 2 * Real.exp (-((n : ℝ) / 1200)) := by
    apply chern_le_of
    have e : ((3 * n : ℕ) : ℝ) - 2 * n = n := by push_cast; ring
    rw [e]
    apply le_min
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · linarith
  set e := Real.exp (-(1 / 8400) * L) with he
  have he0 : 0 < e := Real.exp_pos _
  have hexp : Real.exp (-((n : ℝ) / 1200)) ≤ 2 * e := by
    have : -((n : ℝ) / 1200) ≤ 1 / 1200 + -(1 / 8400) * L := by linarith
    have h2 : Real.exp (1 / 1200) ≤ 2 := by
      calc Real.exp (1 / 1200) ≤ Real.exp ell := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := exp_ell
    calc Real.exp (-((n : ℝ) / 1200)) ≤ Real.exp (1 / 1200 + -(1 / 8400) * L) :=
          Real.exp_le_exp.mpr this
      _ = Real.exp (1 / 1200) * e := Real.exp_add _ _
      _ ≤ 2 * e := by gcongr
  -- the residue-class error `2^{3n₀+3} ≤ 8 x^{0.3}` is negligible against `L_Y ≥ x^{1.001}/4`
  have hpow : (2 : ℝ) ^ (3 * n + 3) ≤ 8 * Real.exp (0.3 * L) := by
    have : (2 : ℝ) ^ (3 * n + 3) = 8 * Real.exp (3 * n * ell) := by
      rw [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm, ← exp_ell, ← Real.exp_nat_mul]
      push_cast; ring_nf
    rw [this]
    have h' : (n : ℝ) * ell ≤ L / 10 := by
      have := mul_le_mul_of_nonneg_right hn1 hl.le
      rwa [show L / (10 * ell) * ell = L / 10 by field_simp] at this
    have h'' : 3 * (n : ℝ) * ell ≤ 0.3 * L := by nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h'') (by norm_num)
  have hpow' : (2 : ℝ) ^ (3 * n + 3) ≤ 32 * e * LYr := by
    have hsplit : Real.exp (0.3 * L) = Real.exp (-(0.701 * L)) * Real.exp (1.001 * L) := by
      rw [← Real.exp_add]; ring_nf
    have hle : Real.exp (-(0.701 * L)) ≤ e := Real.exp_le_exp.mpr (by linarith)
    calc (2 : ℝ) ^ (3 * n + 3) ≤ 8 * Real.exp (0.3 * L) := hpow
      _ = 32 * Real.exp (-(0.701 * L)) * (Real.exp (1.001 * L) / 4) := by rw [hsplit]; ring
      _ ≤ 32 * e * LYr := by gcongr
  have hxd : x ^ (-(1 / 8400 : ℝ)) = e := rpow_eq_exp_Lx hx0 _
  rw [hxd]
  calc (((oddClosed Y).filter (fun N => ¬ crosses x N)).card : ℝ)
      ≤ (((oddClosed Y).filter (fun N => (n : ℝ) / 10 ≤ |(Swd N n : ℝ) - 2 * n|)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ LYr * (chern n ((n : ℝ) / 10) + chern n (((3 * n : ℕ) : ℝ) - 2 * n)) +
        2 ^ (3 * n + 3) := hdev
    _ ≤ LYr * (2 * (2 * e) + 2 * (2 * e)) + 32 * e * LYr := by
        gcongr
        · exact c1.trans (by linarith)
        · exact c2.trans (by linarith)
    _ = 40 * e * LYr := by ring

end CollatzCLT
