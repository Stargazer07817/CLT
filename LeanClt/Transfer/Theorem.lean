import LeanClt.Transfer.Main

/-!
# Theorem 5.10: the asymptotic form

`large2_ev`: the extra numerical conditions hold for large `x`. `transfer`: every error term of
`transfer_error` is `O((log x)^{-A})`, with the smoothing term carrying the constant `C_A` of
Theorem 3.1.
-/

open Real Finset Complex Filter Topology

noncomputable section

namespace CollatzCLT

/-- **The extra conditions hold for large `x`.** -/
theorem large2_ev : ∀ᶠ x : ℝ in atTop, Large2 x := by
  have hc := c_pos'; have hc3 := c_lt_third; have hc4 := c_ge_quarter
  have hl := ell_pos; have hl7 := ell_lt_07; have hl6 := ell_gt
  have e1 := ev_rpow_le_mul (a := 0.6) (ε := 10 ^ (-6 : ℤ)) (by norm_num) (by norm_num)
  have e2 := ev_rpow_le_mul (a := 0.7) (ε := 10 ^ (-4 : ℤ)) (by norm_num) (by norm_num)
  have e3 := ev_rpow_le_mul (a := 0.8) (ε := 10 ^ (-4 : ℤ)) (by norm_num) (by norm_num)
  have e4 := ev_rpow_le_rpow (a := 0.7) (b := 0.8) (ε := 0.1) (by norm_num) (by norm_num)
  have e5 := ev_rpow_le_rpow (a := 0.6) (b := 0.8) (ε := 0.1) (by norm_num) (by norm_num)
  have e6 : ∀ᶠ L : ℝ in atTop, (6 : ℝ) ≤ L ^ (0.8 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.8)).eventually (eventually_ge_atTop 6)
  have e7 : ∀ᶠ L : ℝ in atTop, (4 : ℝ) ≤ L ^ (0.4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.4)).eventually (eventually_ge_atTop 4)
  filter_upwards [ev_of_log e1, ev_of_log e2, ev_of_log e3, ev_of_log e4, ev_of_log e5,
    ev_of_log e6, ev_of_log e7, ev_of_log (eventually_ge_atTop (10 ^ 7 : ℝ))]
    with x h1 h2 h3 h4 h5 h6 h7 hL
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith
  have hm1 := mT_le x (by linarith)
  have hm2 := mT_ge x
  have hn1 := n0_le x (by linarith)
  simp only [← hLdef, alpha_val] at hm1 hm2 hn1
  norm_num at h1 h2 h3 hm1 hm2
  have h06 : 0 ≤ L ^ (0.6 : ℝ) := Real.rpow_nonneg hL0.le _
  have hm0 : (0 : ℝ) ≤ mT x := Nat.cast_nonneg _
  have hnell : ell * (n0 x : ℝ) ≤ L / 10 := by
    have := mul_le_mul_of_nonneg_left hn1 hl.le
    rwa [show ell * (L / (10 * ell)) = L / 10 by field_simp] at this
  have hcm : c * (mT x : ℝ) ≤ 1 / 3 * mT x := mul_le_mul_of_nonneg_right hc3.le hm0
  have hl06 : ell * L ^ (0.6 : ℝ) ≤ 0.7 * L ^ (0.6 : ℝ) := mul_le_mul_of_nonneg_right hl7.le h06
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h7, ?_, ?_⟩
  · linarith
  · rw [alpha_val]; linarith
  · rw [alpha_val]; norm_num; linarith
  · linarith
  · rw [div_le_iff₀ hc]; nlinarith
  · linarith
  · have : L / (10 * ell) ≤ L / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  · rw [alpha_val]; linarith

/-- `L · L^{-(A+1)} = L^{-A}`. -/
lemma mul_rpow_neg_succ {L : ℝ} (hL : 0 < L) (A : ℝ) : L * L ^ (-(A + 1)) = L ^ (-A) := by
  rw [show -(A + 1) = -A - 1 by ring, Real.rpow_sub hL, Real.rpow_one]
  field_simp

/-- A product of a fixed polynomial factor and a stretched exponential, absorbed into `L^{-A}`. -/
lemma ev_absorb (A K : ℝ) {k b : ℝ} (hk : 0 < k) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, K * (L * Real.exp (-(k * L ^ b))) ≤ L ^ (-A) := by
  have h := ev_pow_mul_exp_le 1 (A + 1) hk hb
  filter_upwards [h, eventually_ge_atTop (max K 1), eventually_gt_atTop (0 : ℝ)] with L hL hK hL0
  rw [Real.rpow_one] at hL
  have hK' : K ≤ L := (le_max_left _ _).trans hK
  have hE : 0 ≤ L * Real.exp (-(k * L ^ b)) := by positivity
  calc K * (L * Real.exp (-(k * L ^ b))) ≤ L * (L * Real.exp (-(k * L ^ b))) := by gcongr
    _ ≤ L * L ^ (-(A + 1)) := by gcongr
    _ = L ^ (-A) := mul_rpow_neg_succ hL0 A

/-- **Theorem 5.10 (natural-weight transfer with phase), (5.14).** Assuming Theorem 3.1: for
fixed reals `ρ, η` and every `A > 0`, for all large `x`, uniformly over `Y ∈ [x^α, x^{α²}]`, over
subsets `E' ⊆ 𝓜_x`, over clocks `q` and over all real `s`, (5.14) holds with error
`O_A((log x)^{-A})`. No Diophantine input. -/
theorem transfer (hJM : JointMixing) (ρ η A : ℝ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, ∀ x Y : ℝ, x₀ ≤ x → x ^ alpha ≤ Y → Y ≤ x ^ (alpha ^ 2) →
      ∀ E : Finset ℕ, (↑E : Set ℕ) ⊆ Mset x → ∀ (q : ℕ → ℝ) (s : ℝ),
        ‖transferLHS x Y E q ρ η s - transferRHS x Y E q ρ η s‖ ≤ C * Lx x ^ (-A) := by
  obtain ⟨Cm, hCm0, hmixC⟩ := mix_step hJM (A + 1) (by linarith)
  obtain ⟨BR, hBR⟩ := renewalR_bounded
  obtain ⟨BI, hBI0, hBI⟩ := norm_sum_rinner_le
  set B := max BR BI with hBdef
  have hB0 : 0 ≤ B := hBI0.trans (le_max_right _ _)
  have hκ := κW_pos
  set K5 : ℝ := 2 * 10 ^ 5 with hK5
  have hK50 : 0 < K5 := by norm_num [hK5]
  set C : ℝ := 4 + 40 * Cm * K5 ^ (A + 1) with hC
  have f1 := ev_of_log (ev_absorb A 16 (k := 0.8) (b := 1) (by norm_num) (by norm_num))
  have f2 := ev_of_log (ev_absorb A 80 (k := 1 / 2) (b := 0.2) (by norm_num) (by norm_num))
  have f3 := ev_of_log (ev_absorb A (2 * (160 * (1 + 2 / κW))) (k := κW / 2) (b := 0.6)
    (by positivity) (by norm_num))
  have f4 := ev_of_log (ev_absorb A (2 * (80 * B)) (k := 1 / 2) (b := 0.2) (by norm_num)
    (by norm_num))
  have hev := large_ev.and (large2_ev.and ((typical (A + 1)).and (f1.and (f2.and (f3.and f4)))))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hev
  refine ⟨C, x₀, fun x Y hx hY1 hY2 E hE q s => ?_⟩
  obtain ⟨hL, hL2, htyp, g1, g2, g3, g4⟩ := hx₀ x hx
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  set L := Lx x with hLdef
  have hL0 : 0 < L := by linarith [hL.L_ge]
  have hL1 : 1 ≤ L := by linarith [hL.L_ge]
  have hBR' : ∀ u, ‖renewalR ρ η s u‖ ≤ B := fun u => (hBR ρ η s u).trans (le_max_left _ _)
  have hBI' : ∀ u (I : Finset ℕ), ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ B :=
    fun u I => (hBI ρ η s u I).trans (le_max_right _ _)
  have hmain := transfer_error hL hL2 hY1 hY2 E hE q ρ η s B hB0 hBR' hBI' Cm (A + 1) hCm0
    (fun r hmr hr K => hmixC hL hY0.le E hE q ρ η s hmr hr K) (L ^ (-(A + 1))) (htyp Y hY1)
  rw [← hLdef] at hmain
  refine hmain.trans ?_
  -- bounds on `n₀` and `m`
  have hn6 := hL2.n6
  rw [← hLdef] at hn6
  have hLb : (200000 : ℝ) ≤ L := by have := hL.L_ge; rwa [← hLdef] at this
  have hn0 : (0 : ℝ) ≤ n0 x := Nat.cast_nonneg _
  have hn1L : (n0 x : ℝ) + 1 ≤ L := by linarith
  have hn2L : (n0 x : ℝ) + 2 ≤ L := by linarith
  have hLA : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL0.le _
  have hLA1 : 0 ≤ L ^ (-(A + 1)) := Real.rpow_nonneg hL0.le _
  have hLL := mul_rpow_neg_succ hL0 A
  -- T1
  have T1 : (n0 x + 2) * L ^ (-(A + 1)) ≤ L ^ (-A) := by
    rw [← hLL]; exact mul_le_mul_of_nonneg_right hn2L hLA1
  -- T2
  have T2 : 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y ≤ L ^ (-A) := by
    have hΔ : Δx x ≤ Real.exp (0.2 * L) := Real.exp_le_exp.mpr hL2.nsmall
    have hY : Real.exp L ≤ Y := by
      refine le_trans ?_ hY1
      rw [rpow_eq_exp_Lx hx0, ← hLdef]
      exact Real.exp_le_exp.mpr (by unfold alpha; nlinarith)
    have he1 : 1 ≤ Real.exp (0.2 * L) := Real.one_le_exp (by positivity)
    have hg1 := g1
    rw [Real.rpow_one] at hg1
    have hexp : Real.exp (0.2 * L) / Real.exp L = Real.exp (-(0.8 * L)) := by
      rw [← Real.exp_sub]; ring_nf
    calc 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y
        ≤ 4 * (L * (4 * Real.exp (0.2 * L))) / Real.exp L := by
          gcongr
          · have := (Real.exp_pos (ell * (n0 x + Lx x ^ (0.6 : ℝ)))).le
            unfold Δx; positivity
          · linarith
      _ = 16 * (L * (Real.exp (0.2 * L) / Real.exp L)) := by ring
      _ = 16 * (L * Real.exp (-(0.8 * L))) := by rw [hexp]
      _ ≤ L ^ (-A) := hg1
  -- T3
  have T3 : 40 * ((n0 x + 1) * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))))) ≤ L ^ (-A) := by
    have hg := g2
    calc 40 * ((n0 x + 1) * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))))
        ≤ 40 * (L * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))))) := by gcongr
      _ = 80 * (L * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) := by ring
      _ ≤ L ^ (-A) := hg
  -- T4
  have T4 : 40 * ((n0 x + 1) * (Cm * (mT x : ℝ) ^ (-(A + 1)))) ≤
      40 * Cm * K5 ^ (A + 1) * L ^ (-A) := by
    have hm2 := mT_ge x
    rw [← hLdef, alpha_val] at hm2
    have hmK : L / K5 ≤ mT x := by
      rw [hK5]; have := hL.L_ge; rw [← hLdef] at this; norm_num at hm2 ⊢; linarith
    have hpow : (mT x : ℝ) ^ (-(A + 1)) ≤ (L / K5) ^ (-(A + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hmK (by linarith)
    have hsplit : (L / K5) ^ (-(A + 1)) = K5 ^ (A + 1) * L ^ (-(A + 1)) := by
      rw [Real.div_rpow hL0.le hK50.le, Real.rpow_neg hK50.le, div_eq_mul_inv, inv_inv, mul_comm]
    have hm0 : 0 ≤ (mT x : ℝ) ^ (-(A + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc 40 * ((n0 x + 1) * (Cm * (mT x : ℝ) ^ (-(A + 1))))
        ≤ 40 * (L * (Cm * (K5 ^ (A + 1) * L ^ (-(A + 1))))) := by
          rw [← hsplit]; gcongr
      _ = 40 * Cm * K5 ^ (A + 1) * (L * L ^ (-(A + 1))) := by ring
      _ = 40 * Cm * K5 ^ (A + 1) * L ^ (-A) := by rw [hLL]
  -- T5
  have T5 : 20 * (Tb L + 2 * B * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))))) ≤ L ^ (-A) := by
    have hg3 := g3; have hg4 := g4
    have h02 : L ^ (0.2 : ℝ) ≤ L := by
      calc L ^ (0.2 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    have hT : 20 * Tb L ≤ 160 * (1 + 2 / κW) * (L * Real.exp (-(κW / 2 * L ^ (0.6 : ℝ)))) := by
      unfold Tb
      have he : 0 ≤ Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) := (Real.exp_pos _).le
      have hfac : 1 + 2 * L ^ (0.2 : ℝ) / κW ≤ (1 + 2 / κW) * L := by
        have h1 : 2 * L ^ (0.2 : ℝ) / κW ≤ 2 * L / κW := by gcongr
        have h2 : (1 + 2 / κW) * L = L + 2 * L / κW := by ring
        linarith
      rw [show -(κW / 2 * L ^ (0.6 : ℝ)) = -(κW * L ^ (0.6 : ℝ) / 2) by ring]
      calc 20 * (8 * Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) * (1 + 2 * L ^ (0.2 : ℝ) / κW))
          ≤ 20 * (8 * Real.exp (-(κW * L ^ (0.6 : ℝ) / 2)) * ((1 + 2 / κW) * L)) := by gcongr
        _ = 160 * (1 + 2 / κW) * (L * Real.exp (-(κW * L ^ (0.6 : ℝ) / 2))) := by ring
    have hE : 80 * B * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) ≤
        80 * B * (L * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) := by
      gcongr
      exact le_mul_of_one_le_left (Real.exp_pos _).le hL1
    have h3 : 160 * (1 + 2 / κW) * (L * Real.exp (-(κW / 2 * L ^ (0.6 : ℝ)))) ≤
        L ^ (-A) / 2 := by
      have := hg3; rw [mul_assoc 2] at this; linarith
    have h4 : 80 * B * (L * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))) ≤ L ^ (-A) / 2 := by
      have := hg4; rw [mul_assoc 2] at this; linarith
    calc 20 * (Tb L + 2 * B * (2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ)))))
        = 20 * Tb L + 80 * B * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) := by ring
      _ ≤ L ^ (-A) / 2 + L ^ (-A) / 2 := by linarith
      _ = L ^ (-A) := by ring
  have : C * L ^ (-A) = L ^ (-A) + L ^ (-A) + L ^ (-A) + 40 * Cm * K5 ^ (A + 1) * L ^ (-A) +
      L ^ (-A) := by rw [hC]; ring
  rw [this]
  have := add_le_add (add_le_add (add_le_add (add_le_add T1 T2) T3) T4) T5
  linarith

end CollatzCLT
