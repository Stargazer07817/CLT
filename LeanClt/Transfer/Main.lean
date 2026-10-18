import LeanClt.Transfer.Depths

/-!
# Theorem 5.10 (natural-weight transfer with phase)

`transfer_error`: for one threshold `x` satisfying the numerical conditions, the explicit error
in (5.14) is a sum of five terms:

1. atypical sources (Lemma 5.1): `(n₀ + 2) #{¬typical}/L_Y`;
2. offset removal: `|J_Y| (2Δ + 2)/L_Y`;
3. atypical totals on the geometric side: `|J_Y| 10Y P(|S_r - 2r| ≥ L^{0.6})/L_Y`;
4. smoothing (Theorem 3.1): `|J_Y| 10Y C_A m^{-A}/L_Y`;
5. depth restoration and the cutoff: `5Y (T_b + 2B P(|S_m - 2m| ≥ L^{0.6}))/L_Y`.

`transfer` then checks that each is `O((log x)^{-A})`.
-/

open Real Finset Complex Filter

noncomputable section

namespace CollatzCLT

/-- `chern j (L^{0.6}) ≤ 2 e^{-L^{0.2}/2}` for `1 ≤ j ≤ L/6`, `L^{0.4} ≥ 4`. -/
lemma chern_L06_le {L : ℝ} (hL0 : 0 < L) (h04 : 4 ≤ L ^ (0.4 : ℝ)) {j : ℕ} (hj1 : 1 ≤ j)
    (hjL : 6 * (j : ℝ) ≤ L) : chern j (L ^ (0.6 : ℝ)) ≤ 2 * Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast hj1
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

/-- The depth window reindexed by the tail length `t = r - m`. -/
def Iset (x Y : ℝ) : Finset ℕ := (range (n0 x + 1)).filter (fun t => t + mT x ∈ JY x Y)

lemma not_Iset {x Y : ℝ} {t : ℕ} (ht : t ∉ Iset x Y) : t + mT x ∉ JY x Y := by
  intro h
  apply ht
  unfold Iset
  rw [mem_filter, mem_range]
  refine ⟨?_, h⟩
  unfold JY at h
  rw [mem_filter, mem_range] at h
  omega

lemma sum_JY_eq {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    (f : ℕ → ℂ) : ∑ r ∈ JY x Y, f (r - mT x) = ∑ t ∈ Iset x Y, f t := by
  refine Finset.sum_nbij' (fun r => r - mT x) (fun t => t + mT x) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    have hb := JY_bounds hL hY1 hY2 hr
    unfold Iset
    rw [mem_filter, mem_range, Nat.sub_add_cancel hb.1]
    exact ⟨by omega, hr⟩
  · intro t ht
    unfold Iset at ht
    rw [mem_filter] at ht
    exact ht.2
  · intro r hr
    have hb := JY_bounds hL hY1 hY2 hr
    exact Nat.sub_add_cancel hb.1
  · intro t _
    exact Nat.add_sub_cancel t (mT x)
  · intro r _; rfl

open Classical in
/-- The right side of (5.14), times `L_Y`, in word–target form. -/
lemma LY_mul_RHS {x Y : ℝ} (hY0 : 0 < Y) (hLY : (LY Y : ℝ) ≠ 0) (E : Finset ℕ) (q : ℕ → ℝ)
    (ρ η s : ℝ) :
    (LY Y : ℂ) * transferRHS x Y E q ρ η s =
      ∑ M ∈ E, ∑ S1 ∈ Icc (mT x) (3 * mT x), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
        (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
          renewalR ρ η s (uMS Y M S1 (mT x))) := by
  unfold transferRHS
  rw [← mul_assoc, show (LY Y : ℂ) * ((Y / (oddClosed Y).card : ℝ) : ℂ) = (Y : ℂ) by
    rw [show ((oddClosed Y).card : ℝ) = (LY Y : ℝ) from rfl]
    push_cast
    field_simp [show (LY Y : ℂ) ≠ 0 by exact_mod_cast hLY]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S1 _ => ?_
  unfold muJ uMS phase
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h1
  · push_cast; ring
  · simp

/-- The identity summed over `r ∈ J_Y`. -/
lemma sum_identity {x Y : ℝ} (hL : Large x) (hY1 : x ^ alpha ≤ Y) (hY2 : Y ≤ x ^ (alpha ^ 2))
    (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ) (ρ η s : ℝ) {K : ℕ}
    (hK : 2 * Y * 3 ^ n0 x < 2 ^ K) :
    ∑ r ∈ JY x Y, ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
        (Qop r (mT x) (muJ r) S z : ℂ) * Gt Y E q ρ η s r S z =
      ∑ M ∈ E, ∑ S1 ∈ range (K + 1), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
        (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
          ∑ t ∈ Iset x Y, rinner ρ η s (uMS Y M S1 (mT x)) t) := by
  obtain ⟨hx0, -, -, hY0⟩ := large_facts hL hY1
  have hEpos : ∀ M ∈ E, 0 < M := fun M hM => (hE hM).1.pos
  have hstep : ∀ r ∈ JY x Y, ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
        (Qop r (mT x) (muJ r) S z : ℂ) * Gt Y E q ρ η s r S z =
      ∑ M ∈ E, ∑ S1 ∈ range (K + 1), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
        (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
          rinner ρ η s (uMS Y M S1 (mT x)) (r - mT x)) := by
    intro r hr
    have hb := JY_bounds hL hY1 hY2 hr
    obtain ⟨t, rfl⟩ : ∃ t, r = mT x + t := ⟨r - mT x, by omega⟩
    rw [show mT x + t - mT x = t by omega]
    refine depth_identity hY0 E hEpos q ρ η s (mT x) t K fun S M hM hw => ?_
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hEpos M hM
    have h2 := hw.2
    rw [div_le_iff₀ (by positivity)] at h2
    have h3 : (3 : ℝ) ^ (mT x + t) ≤ 3 ^ n0 x := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ S < 2 ^ K := by
      have : (2 : ℝ) ^ S ≤ 2 ^ S * M := le_mul_of_one_le_right (by positivity) hM1
      nlinarith
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h4
    omega
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S1 _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    sum_JY_eq hL hY1 hY2 (fun t => rinner ρ η s (uMS Y M S1 (mT x)) t)]

lemma sum_JY_norm_le {x Y : ℝ} (f : ℕ → ℂ) {b : ℝ} (hb0 : 0 ≤ b) (hf : ∀ r ∈ JY x Y, ‖f r‖ ≤ b) :
    ‖∑ r ∈ JY x Y, f r‖ ≤ (n0 x + 1) * b := by
  calc ‖∑ r ∈ JY x Y, f r‖ ≤ ∑ r ∈ JY x Y, ‖f r‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ JY x Y, b := Finset.sum_le_sum hf
    _ = (JY x Y).card * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n0 x + 1) * b := by
        gcongr
        exact_mod_cast card_JY_le x Y

-- a long assembly of five error terms
set_option maxHeartbeats 1000000 in
open Classical in
/-- **Theorem 5.10 with an explicit error, for one threshold.** -/
theorem transfer_error {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ)
    (ρ η s B : ℝ) (hB0 : 0 ≤ B) (hBR : ∀ u, ‖renewalR ρ η s u‖ ≤ B)
    (hBI : ∀ u (I : Finset ℕ), ‖∑ t ∈ I, rinner ρ η s u t‖ ≤ B) (Cm A2 : ℝ) (hCm : 0 ≤ Cm)
    (hmix : ∀ r : ℕ, mT x ≤ r → r + mT x ≤ n0 x → ∀ K : ℕ,
      ‖∑ S ∈ range (K + 1),
          (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) -
        ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
          (Qop r (mT x) (muJ r) S z : ℂ) * Gt Y E q ρ η s r S z‖ ≤
      10 * Y * (Cm * (mT x : ℝ) ^ (-A2)))
    (Ng : ℝ) (hNg : (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) ≤ Ng * LY Y) :
    ‖transferLHS x Y E q ρ η s - transferRHS x Y E q ρ η s‖ ≤
      (n0 x + 2) * Ng + 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y +
        40 * ((n0 x + 1) * (2 * Real.exp (-(1 / 2 * Lx x ^ (0.2 : ℝ))))) +
        40 * ((n0 x + 1) * (Cm * (mT x : ℝ) ^ (-A2))) +
        20 * (Tb (Lx x) + 2 * B * (2 * Real.exp (-(1 / 2 * Lx x ^ (0.2 : ℝ))))) := by
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hLL : 0 < Lx x := by linarith [hL.L_ge]
  have hLY4 : Y / 4 ≤ (LY Y : ℝ) := by have := LY_ge hY0.le; linarith
  have hLYpos : (0 : ℝ) < LY Y := lt_of_lt_of_le (by positivity) hLY4
  have hEo : ∀ M ∈ E, Odd M := fun M hM => (hE hM).1
  set m := mT x with hm
  -- the cutoff `K`
  obtain ⟨K0, hK0⟩ := pow_unbounded_of_one_lt (2 * Y * 3 ^ n0 x) (by norm_num : (1 : ℝ) < 2)
  set K := max K0 (3 * m) with hKdef
  have hK : 2 * Y * 3 ^ n0 x < 2 ^ K :=
    hK0.trans_le (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))
  have hK3 : 3 * m ≤ K := le_max_right _ _
  have hch : ∀ r ∈ JY x Y, chern r (Lx x ^ (0.6 : ℝ)) ≤
      2 * Real.exp (-(1 / 2 * Lx x ^ (0.2 : ℝ))) := by
    intro r hr
    have hb := JY_bounds hL hY1 hY2 hr
    refine chern_L06_le hLL hL2.l04 (le_trans hL.m_ge hb.1) ?_
    have : (r : ℝ) ≤ n0 x := by exact_mod_cast (show r ≤ n0 x by omega)
    linarith [hL2.n6]
  have hchm : chern m (Lx x ^ (0.6 : ℝ)) ≤ 2 * Real.exp (-(1 / 2 * Lx x ^ (0.2 : ℝ))) := by
    refine chern_L06_le hLL hL2.l04 hL.m_ge ?_
    have : (m : ℝ) ≤ n0 x := by exact_mod_cast (show m ≤ n0 x by have := two_m_le_n0 hL; omega)
    linarith [hL2.n6]
  -- the five pieces
  set Wr : ℕ → ℂ := fun r => ∑ S ∈ range (K + 1), if typT x r S then
    (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) else 0 with hWr
  set Vr : ℕ → ℂ := fun r => ∑ S ∈ range (K + 1),
    (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) with hVr
  set Qr : ℕ → ℂ := fun r => ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
    (Qop r m (muJ r) S z : ℂ) * Gt Y E q ρ η s r S z with hQr
  have eA := lhs_decomp hL hY1 hY2 E hE q ρ η s
  have eB : ‖∑ r ∈ JY x Y, (depthSum x Y E q ρ η s r - Wr r)‖ ≤
      (n0 x + 1) * (2 * Δx x + 2) :=
    sum_JY_norm_le _ (by have := (Real.exp_pos (ell * (n0 x + Lx x ^ (0.6 : ℝ)))).le
                         unfold Δx; linarith)
      fun r hr => depth_offset hL hY1 E hEo q ρ η s
        (by have := (JY_bounds hL hY1 hY2 hr).2; omega) hK
  set ch := 2 * Real.exp (-(1 / 2 * Lx x ^ (0.2 : ℝ))) with hchdef
  have hch0 : 0 ≤ ch := by positivity
  have eC : ‖∑ r ∈ JY x Y, (Wr r - Vr r)‖ ≤ (n0 x + 1) * (10 * Y * ch) :=
    sum_JY_norm_le _ (by positivity) fun r hr => by
      have hb := JY_bounds hL hY1 hY2 hr
      refine (restore_typ hL hY0.le E hE q ρ η s (le_trans hL.m_ge hb.1) hb.2 K).trans ?_
      exact mul_le_mul_of_nonneg_left (hch r hr) (by positivity)
  have hmA : 0 ≤ Cm * (m : ℝ) ^ (-A2) := mul_nonneg hCm (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have eD : ‖∑ r ∈ JY x Y, (Vr r - Qr r)‖ ≤ (n0 x + 1) * (10 * Y * (Cm * (m : ℝ) ^ (-A2))) :=
    sum_JY_norm_le _ (by positivity) fun r hr =>
      hmix r (JY_bounds hL hY1 hY2 hr).1 (JY_bounds hL hY1 hY2 hr).2 K
  have eQ := sum_identity hL hY1 hY2 E hE q ρ η s hK
  have eR := LY_mul_RHS (x := x) hY0 hLYpos.ne' E q ρ η s
  have eE := renewal_side hL hL2 hY1 hY2 E hE q ρ η s B hB0 hBR hBI hK3 (Iset x Y)
    (fun t ht => not_Iset ht)
  have hTb := Tb_nonneg hLL.le
  have eE' : 5 * Y * (Tb (Lx x) + 2 * B * chern m (Lx x ^ (0.6 : ℝ))) ≤
      5 * Y * (Tb (Lx x) + 2 * B * ch) := by gcongr
  have eA' : (n0 x + 2) * (((oddClosed Y).filter (fun N => ¬ Good x N)).card : ℝ) ≤
      (n0 x + 2) * (Ng * LY Y) := by gcongr
  set z := transferLHS x Y E q ρ η s - transferRHS x Y E q ρ η s with hz
  have hdecomp : (LY Y : ℂ) * z =
      ((LY Y : ℂ) * transferLHS x Y E q ρ η s - ∑ r ∈ JY x Y, depthSum x Y E q ρ η s r) +
      ∑ r ∈ JY x Y, (depthSum x Y E q ρ η s r - Wr r) + ∑ r ∈ JY x Y, (Wr r - Vr r) +
      ∑ r ∈ JY x Y, (Vr r - Qr r) +
      ((∑ M ∈ E, ∑ S1 ∈ range (K + 1), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
          (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
            ∑ t ∈ Iset x Y, rinner ρ η s (uMS Y M S1 (mT x)) t)) -
        ∑ M ∈ E, ∑ S1 ∈ Icc (mT x) (3 * mT x), (muJ (mT x) S1 (M : ZMod (3 ^ mT x)) : ℂ) *
          (((Y * 3 ^ mT x / M : ℝ) : ℂ) * phase q ρ η s M S1 (mT x) *
            renewalR ρ η s (uMS Y M S1 (mT x)))) := by
    rw [hz, mul_sub, eR, ← eQ, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    ring
  have htot : ‖(LY Y : ℂ) * z‖ ≤ (n0 x + 2) * (Ng * LY Y) + (n0 x + 1) * (2 * Δx x + 2) +
      (n0 x + 1) * (10 * Y * ch) + (n0 x + 1) * (10 * Y * (Cm * (m : ℝ) ^ (-A2))) +
      5 * Y * (Tb (Lx x) + 2 * B * ch) := by
    rw [hdecomp]
    refine (norm_add_le _ _).trans (add_le_add ?_ (eE.trans eE'))
    refine (norm_add_le _ _).trans (add_le_add ?_ eD)
    refine (norm_add_le _ _).trans (add_le_add ?_ eC)
    exact (norm_add_le _ _).trans (add_le_add (eA.trans eA') eB)
  rw [norm_mul, Complex.norm_natCast] at htot
  have hNg0 : 0 ≤ Ng * LY Y := le_trans (Nat.cast_nonneg _) hNg
  have hΔ0 : 0 ≤ Δx x := (Real.exp_pos _).le
  have hn0 : (0 : ℝ) ≤ n0 x := Nat.cast_nonneg _
  refine le_of_mul_le_mul_right (a := (LY Y : ℝ)) ?_ hLYpos
  rw [mul_comm ‖z‖]
  refine htot.trans ?_
  have hY4 : Y ≤ 4 * (LY Y : ℝ) := by linarith
  have h1 : (n0 x + 1) * (2 * Δx x + 2) ≤ 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y * LY Y := by
    have hP : 0 ≤ (n0 x + 1) * (2 * Δx x + 2) := by positivity
    calc (n0 x + 1) * (2 * Δx x + 2) = (n0 x + 1) * (2 * Δx x + 2) / Y * Y := by
          field_simp
      _ ≤ (n0 x + 1) * (2 * Δx x + 2) / Y * (4 * LY Y) :=
          mul_le_mul_of_nonneg_left hY4 (by positivity)
      _ = 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y * LY Y := by ring
  have h2 : (n0 x + 1) * (10 * Y * ch) ≤ 40 * ((n0 x + 1) * ch) * LY Y := by
    calc (n0 x + 1) * (10 * Y * ch) = 10 * ((n0 x + 1) * ch) * Y := by ring
      _ ≤ 10 * ((n0 x + 1) * ch) * (4 * LY Y) := mul_le_mul_of_nonneg_left hY4 (by positivity)
      _ = 40 * ((n0 x + 1) * ch) * LY Y := by ring
  have h3 : (n0 x + 1) * (10 * Y * (Cm * (m : ℝ) ^ (-A2))) ≤
      40 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) * LY Y := by
    calc (n0 x + 1) * (10 * Y * (Cm * (m : ℝ) ^ (-A2))) =
          10 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) * Y := by ring
      _ ≤ 10 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) * (4 * LY Y) :=
          mul_le_mul_of_nonneg_left hY4 (by positivity)
      _ = 40 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) * LY Y := by ring
  have h4 : 5 * Y * (Tb (Lx x) + 2 * B * ch) ≤ 20 * (Tb (Lx x) + 2 * B * ch) * LY Y := by
    calc 5 * Y * (Tb (Lx x) + 2 * B * ch) = 5 * (Tb (Lx x) + 2 * B * ch) * Y := by ring
      _ ≤ 5 * (Tb (Lx x) + 2 * B * ch) * (4 * LY Y) :=
          mul_le_mul_of_nonneg_left hY4 (by positivity)
      _ = 20 * (Tb (Lx x) + 2 * B * ch) * LY Y := by ring
  have h0 : (n0 x + 2) * (Ng * LY Y) = (n0 x + 2) * Ng * LY Y := by ring
  have hexp : ((n0 x + 2) * Ng + 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y +
      40 * ((n0 x + 1) * ch) + 40 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) +
      20 * (Tb (Lx x) + 2 * B * ch)) * LY Y =
      (n0 x + 2) * Ng * LY Y + 4 * ((n0 x + 1) * (2 * Δx x + 2)) / Y * LY Y +
      40 * ((n0 x + 1) * ch) * LY Y + 40 * ((n0 x + 1) * (Cm * (m : ℝ) ^ (-A2))) * LY Y +
      20 * (Tb (Lx x) + 2 * B * ch) * LY Y := by ring
  rw [hexp]
  linarith only [h0, h1, h2, h3, h4]

end CollatzCLT
