import LeanClt.Transfer.Theorem

/-!
# Theorem 5.10, the scalar formula (5.15)

At `s = 0`, (5.14) reads `P(𝓔') = (Y/L_Y) ∑_M (3^m/M) E[1{X_m ≡ M} 1{S_m ≤ 3m} R₀(u)] + O(L^{-A})`.
For a typical `S_m`, `u ≥ L^{0.8}` and Theorem 4.1 at `s = 0` gives `R₀(u) = 1/c + O(u^{-δ})`;
atypical `S_m` (including `S_m > 3m`) have geometric weight `≤ P(|S_m - 2m| ≥ L^{0.6})`,
controlled by the harmonic bound at depth `m`. Finally `Y/L_Y = 2 + O(1/Y)`.
-/

open Real Finset Complex Filter

noncomputable section

namespace CollatzCLT

open Classical in
lemma transferLHS_zero (x Y : ℝ) (E : Finset ℕ) (q : ℕ → ℝ) (ρ η : ℝ) :
    transferLHS x Y E q ρ η 0 = (eventProb x Y E : ℂ) := by
  unfold transferLHS eventProb
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  push_cast
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

lemma Y_sub_LY {Y : ℝ} (hY : 0 ≤ Y) : |Y - 2 * LY Y| ≤ 3 := by
  have h := abs_le.mp (LY_bound hY)
  have h1 : (⌈Y⌉₊ : ℝ) < Y + 1 := Nat.ceil_lt_add_one hY
  have h1' : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  have h2 : 2 * Y < (⌊2 * Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2' : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hle := oddClosed_bounds hY
  have hc : ((⌊2 * Y⌋₊ + 1 - ⌈Y⌉₊ : ℕ) : ℝ) = (⌊2 * Y⌋₊ : ℝ) + 1 - ⌈Y⌉₊ := by
    rw [Nat.cast_sub hle]; push_cast; ring
  rw [hc] at h
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-- `phase` at frequency zero. -/
lemma phase_zero (q : ℕ → ℝ) (ρ η : ℝ) (M S r : ℕ) : phase q ρ η 0 M S r = 1 := by
  unfold phase; simp

lemma muJ_le_lawS (n s : ℕ) (z : ZMod (3 ^ n)) : muJ n s z ≤ lawS n s := by
  rw [← sum_muJ]
  exact Finset.single_le_sum (fun y _ => muJ_nonneg n s y) (Finset.mem_univ z)

/-- **The scalar estimate for one threshold.** -/
theorem scalar_error {x Y : ℝ} (hL : Large x) (hL2 : Large2 x) (hY1 : x ^ alpha ≤ Y)
    (hY2 : Y ≤ x ^ (alpha ^ 2)) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x)
    (B CR δ : ℝ) (hB : ∀ u, ‖renewalR 0 0 0 u‖ ≤ B) (hCR0 : 0 ≤ CR) (hδ : 0 < δ)
    (hCR : ∀ u, 2 ≤ u → ‖renewalR 0 0 0 u - (1 / c : ℂ)‖ ≤ CR * u ^ (-δ)) :
    |eventProb x Y E - 2 / c * ∑ M ∈ E, (3 : ℝ) ^ mT x / M * probXm (mT x) M| ≤
      ‖transferLHS x Y E (fun _ => 0) 0 0 0 - transferRHS x Y E (fun _ => 0) 0 0 0‖ +
        20 * (CR * Lx x ^ (-(0.8 * δ)) + (B + 1 / c) * chern (mT x) (Lx x ^ (0.6 : ℝ))) +
        60 / (c * Y) + 10 / c * chern (mT x) (Lx x ^ (0.6 : ℝ)) := by
  classical
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hc := c_pos'
  set m := mT x with hm
  set L := Lx x with hLdef
  have hLb : (200000 : ℝ) ≤ L := hL.L_ge
  have hL0 : 0 < L := by linarith
  have hm1 : 1 ≤ m := hL.m_ge
  have hLY4 : Y / 4 ≤ (LY Y : ℝ) := by have := LY_ge hY0.le; linarith
  have hLYpos : (0 : ℝ) < LY Y := lt_of_lt_of_le (by positivity) hLY4
  set ch := chern m (L ^ (0.6 : ℝ)) with hch
  have hch0 : 0 ≤ ch := by rw [hch]; unfold chern; positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set w : ℕ → ℕ → ℝ := fun M S => (3 : ℝ) ^ m / M * muJ m S (M : ZMod (3 ^ m)) with hw
  have hw0 : ∀ M S, 0 ≤ w M S := fun M S => by
    simp only [hw]; have := muJ_nonneg m S (M : ZMod (3 ^ m)); positivity
  have hwS : ∀ S, ∑ M ∈ E, w M S ≤ 5 * lawS m S := fun S =>
    sum_E_muJ_le hL E hE (two_m_le_n0 hL) S
  have hwsum : ∀ M, Summable (fun S => w M S) := fun M =>
    Summable.of_nonneg_of_le (fun S => hw0 M S)
      (fun S => mul_le_mul_of_nonneg_left (muJ_le_lawS m S _) (by positivity))
      ((summable_lawS m).mul_left _)
  -- the two geometric masses
  set A1 := ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), w M S with hA1
  set A2 := ∑ M ∈ E, ∑' S, w M S with hA2
  have hA1le : A1 ≤ 5 := by
    rw [hA1, Finset.sum_comm]
    calc ∑ S ∈ Icc m (3 * m), ∑ M ∈ E, w M S ≤ ∑ S ∈ Icc m (3 * m), 5 * lawS m S :=
          Finset.sum_le_sum fun S _ => hwS S
      _ = 5 * ∑ S ∈ Icc m (3 * m), lawS m S := by rw [Finset.mul_sum]
      _ ≤ 5 * 1 := by
          gcongr
          have := (summable_lawS m).sum_le_tsum (Icc m (3 * m)) (fun i _ => lawS_nonneg m i)
          rwa [tsum_lawS] at this
      _ = 5 := by ring
  have hA0 : 0 ≤ A1 := Finset.sum_nonneg fun M _ => Finset.sum_nonneg fun S _ => hw0 M S
  have hA21 : A1 ≤ A2 ∧ A2 - A1 ≤ 5 * ch := by
    have hswap : A2 = ∑' S, ∑ M ∈ E, w M S := by
      rw [hA2, Summable.tsum_finsetSum (fun M _ => hwsum M)]
    have hsum : Summable (fun S => ∑ M ∈ E, w M S) := summable_sum fun M _ => hwsum M
    have hsplit := tsum_eq_sum_add_tsum_ite_real hsum (Icc m (3 * m))
    have hA1' : A1 = ∑ S ∈ Icc m (3 * m), ∑ M ∈ E, w M S := by rw [hA1, Finset.sum_comm]
    have htail0 : 0 ≤ ∑' S, (if S ∈ Icc m (3 * m) then 0 else ∑ M ∈ E, w M S) :=
      tsum_nonneg fun S => by
        split_ifs
        · exact le_rfl
        · exact Finset.sum_nonneg fun M _ => hw0 M S
    have htail : ∑' S, (if S ∈ Icc m (3 * m) then 0 else ∑ M ∈ E, w M S) ≤ 5 * ch := by
      have hm6 := hL2.m6
      have hs2 : Summable (fun S : ℕ => 5 * (if L ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * m| then
          lawS m S else 0)) := (summable_ite_lawS m _).mul_left 5
      have hs1 : Summable (fun S => if S ∈ Icc m (3 * m) then 0 else ∑ M ∈ E, w M S) :=
        Summable.of_nonneg_of_le (fun S => by
          split_ifs
          · exact le_rfl
          · exact Finset.sum_nonneg fun M _ => hw0 M S) (fun S => by
            split_ifs
            · exact Finset.sum_nonneg fun M _ => hw0 M S
            · exact le_rfl) hsum
      calc ∑' S, (if S ∈ Icc m (3 * m) then 0 else ∑ M ∈ E, w M S)
          ≤ ∑' S : ℕ, 5 * (if L ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * m| then lawS m S else 0) := by
            refine Summable.tsum_le_tsum (fun S => ?_) hs1 hs2
            by_cases hS : S ∈ Icc m (3 * m)
            · rw [if_pos hS]; split_ifs <;> simp [lawS_nonneg]
            · rw [if_neg hS]
              have hdev : L ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * m| := by
                rw [mem_Icc, not_and_or] at hS
                rcases hS with h | h
                · have h' : (S : ℝ) + 1 ≤ m := by exact_mod_cast (not_le.mp h)
                  rw [abs_of_neg (by linarith)]; linarith
                · have h' : 3 * (m : ℝ) + 1 ≤ S := by exact_mod_cast (not_le.mp h)
                  rw [abs_of_pos (by linarith)]; linarith
              rw [if_pos hdev]
              exact hwS S
        _ = 5 * ∑' S : ℕ, (if L ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * m| then lawS m S else 0) :=
            tsum_mul_left
        _ ≤ 5 * ch := by
            gcongr
            exact lawS_chernoff hm1 (Real.rpow_nonneg hL0.le _)
    rw [hswap, hsplit, ← hA1']
    constructor <;> linarith
  -- the kernel error per target and coarse total
  have hδ8 : 0 ≤ L ^ (-(0.8 * δ)) := Real.rpow_nonneg hL0.le _
  have hcl : (0 : ℝ) ≤ 1 / c := by positivity
  set e : ℕ → ℝ := fun S => CR * L ^ (-(0.8 * δ)) + (if typT x m S then 0 else B + 1 / c)
    with he
  have he0 : ∀ S, 0 ≤ e S := fun S => by
    simp only [he]; split_ifs <;> positivity
  have hterm : ∀ M ∈ E, ∀ S, ‖renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ)‖ ≤ e S := by
    intro M hM S
    by_cases hT : typT x m S
    · simp only [he, hT, ↓reduceIte, add_zero]
      obtain ⟨hu1, -, -⟩ := u_bounds hL hL2 hY1 hY2 (hE hM) hT
      have h08 : 0 < L ^ (0.8 : ℝ) := Real.rpow_pos_of_pos hL0 _
      have h2 : (2 : ℝ) ≤ L ^ (0.8 : ℝ) := by
        refine le_trans ?_ hL2.xw
        rw [le_div_iff₀ hc, c_eq]
        have : ell < bet := Real.log_lt_log (by norm_num) (by norm_num)
        linarith
      refine (hCR _ (h2.trans hu1)).trans ?_
      gcongr
      calc uMS Y M S m ^ (-δ) ≤ (L ^ (0.8 : ℝ)) ^ (-δ) :=
            Real.rpow_le_rpow_of_nonpos h08 hu1 (by linarith)
        _ = L ^ (-(0.8 * δ)) := by rw [← Real.rpow_mul hL0.le]; ring_nf
    · simp only [he, hT, ↓reduceIte]
      calc ‖renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ)‖
          ≤ ‖renewalR 0 0 0 (uMS Y M S m)‖ + ‖(1 / c : ℂ)‖ := norm_sub_le _ _
        _ ≤ B + 1 / c := by
            gcongr
            · exact hB _
            · rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ CR * L ^ (-(0.8 * δ)) + (B + 1 / c) := by
            have : 0 ≤ CR * L ^ (-(0.8 * δ)) := mul_nonneg hCR0 hδ8
            linarith
  have hX : ‖∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
      (renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ))‖ ≤ 5 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) := by
    calc _ ≤ ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), w M S * e S :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun M hM => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun S _ => by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 M S)]
              exact mul_le_mul_of_nonneg_left (hterm M hM S) (hw0 M S)))
      _ = ∑ S ∈ Icc m (3 * m), e S * ∑ M ∈ E, w M S := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun M _ => by ring
      _ ≤ ∑ S ∈ Icc m (3 * m), e S * (5 * lawS m S) :=
          Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hwS S) (he0 S)
      _ = 5 * (CR * L ^ (-(0.8 * δ)) * ∑ S ∈ Icc m (3 * m), lawS m S +
            (B + 1 / c) * ∑ S ∈ Icc m (3 * m), (if typT x m S then 0 else lawS m S)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp only [he]; split_ifs <;> ring
      _ ≤ 5 * (CR * L ^ (-(0.8 * δ)) * 1 + (B + 1 / c) * ch) := by
          gcongr
          · have := (summable_lawS m).sum_le_tsum (Icc m (3 * m)) (fun i _ => lawS_nonneg m i)
            rwa [tsum_lawS] at this
          · refine le_trans ?_ (lawS_chernoff hm1 (Real.rpow_nonneg hL0.le _))
            refine le_trans ?_ ((summable_ite_lawS m (fun A : ℕ =>
              L ^ (0.6 : ℝ) ≤ |(A : ℝ) - 2 * m|)).sum_le_tsum (Icc m (3 * m))
                (fun i _ => by split_ifs <;> simp [lawS_nonneg]))
            refine Finset.sum_le_sum fun S _ => ?_
            by_cases hT : typT x m S
            · rw [if_pos hT]; split_ifs <;> simp [lawS_nonneg]
            · rw [if_neg hT, if_pos]
              unfold typT at hT; push Not at hT; exact hT.le
      _ = 5 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) := by ring
  -- the right side at `s = 0`
  have hRHS : transferRHS x Y E (fun _ => 0) 0 0 0 = ((Y / LY Y : ℝ) : ℂ) *
      ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) * renewalR 0 0 0 (uMS Y M S m) := by
    have h := LY_mul_RHS (x := x) hY0 hLYpos.ne' E (fun _ => 0) 0 0 0
    simp only [phase_zero, mul_one] at h
    have hLYc : (LY Y : ℂ) ≠ 0 := by exact_mod_cast hLYpos.ne'
    have : transferRHS x Y E (fun _ => 0) 0 0 0 =
        (LY Y : ℂ)⁻¹ * ((LY Y : ℂ) * transferRHS x Y E (fun _ => 0) 0 0 0) := by
      field_simp
    rw [this, h, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [hw]
    rw [← hm]
    push_cast
    field_simp
  have hT : ∑ M ∈ E, (3 : ℝ) ^ m / M * probXm m M = A2 := by
    rw [hA2]
    refine Finset.sum_congr rfl fun M _ => ?_
    unfold probXm
    rw [← tsum_mul_left]
  rw [hT]
  -- assemble
  have hLHS := transferLHS_zero x Y E (fun _ => 0) 0 0
  have hsplitR : ((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
        renewalR 0 0 0 (uMS Y M S m) - ((2 / c * A2 : ℝ) : ℂ) =
      ((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
        (renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ)) +
      ((Y / LY Y * (1 / c) * A1 - 2 / c * A2 : ℝ) : ℂ) := by
    rw [hA1]
    push_cast
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hYLY : |Y / LY Y - 2| ≤ 12 / Y := by
    rw [show Y / LY Y - 2 = (Y - 2 * LY Y) / LY Y by field_simp, abs_div,
      abs_of_pos hLYpos, div_le_div_iff₀ hLYpos hY0]
    have := Y_sub_LY hY0.le
    nlinarith [abs_nonneg (Y - 2 * LY Y)]
  have hYLY4 : Y / LY Y ≤ 4 := by rw [div_le_iff₀ hLYpos]; linarith
  have hscal : |Y / LY Y * (1 / c) * A1 - 2 / c * A2| ≤ 60 / (c * Y) + 10 / c * ch := by
    have e1 : Y / LY Y * (1 / c) * A1 - 2 / c * A2 =
        (1 / c) * ((Y / LY Y - 2) * A1) - 2 / c * (A2 - A1) := by ring
    rw [e1]
    have h1 : |(1 / c) * ((Y / LY Y - 2) * A1)| ≤ 60 / (c * Y) := by
      rw [abs_mul, abs_of_pos (by positivity), abs_mul, abs_of_nonneg hA0]
      calc 1 / c * (|Y / LY Y - 2| * A1) ≤ 1 / c * (12 / Y * 5) := by gcongr
        _ = 60 / (c * Y) := by field_simp; ring
    have h2 : |2 / c * (A2 - A1)| ≤ 10 / c * ch := by
      rw [abs_mul, abs_of_pos (by positivity), abs_of_nonneg (by linarith [hA21.1])]
      calc 2 / c * (A2 - A1) ≤ 2 / c * (5 * ch) := by gcongr; exact hA21.2
        _ = 10 / c * ch := by ring
    calc _ ≤ |(1 / c) * ((Y / LY Y - 2) * A1)| + |2 / c * (A2 - A1)| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have hfin : ((eventProb x Y E - 2 / c * A2 : ℝ) : ℂ) =
      (transferLHS x Y E (fun _ => 0) 0 0 0 - transferRHS x Y E (fun _ => 0) 0 0 0) +
      (((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
        (renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ)) +
      ((Y / LY Y * (1 / c) * A1 - 2 / c * A2 : ℝ) : ℂ)) := by
    rw [← hsplitR, hLHS, hRHS]; push_cast; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hfin]
  have hn1 : ‖((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
      (renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ))‖ ≤
      20 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc Y / LY Y * _ ≤ 4 * (5 * (CR * L ^ (-(0.8 * δ)) + (B + 1 / c) * ch)) :=
          mul_le_mul hYLY4 hX (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hn2 : ‖((Y / LY Y * (1 / c) * A1 - 2 / c * A2 : ℝ) : ℂ)‖ ≤ 60 / (c * Y) + 10 / c * ch := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hscal
  calc _ ≤ ‖transferLHS x Y E (fun _ => 0) 0 0 0 - transferRHS x Y E (fun _ => 0) 0 0 0‖ +
        (‖((Y / LY Y : ℝ) : ℂ) * ∑ M ∈ E, ∑ S ∈ Icc m (3 * m), (w M S : ℂ) *
          (renewalR 0 0 0 (uMS Y M S m) - (1 / c : ℂ))‖ +
        ‖((Y / LY Y * (1 / c) * A1 - 2 / c * A2 : ℝ) : ℂ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := by linarith

/-- **Theorem 5.10, the scalar formula (5.15).** With Rhin's measure, there is `δ₀ > 0` depending
only on `ϰ` such that `P(𝓔') = (2/c) ∑_{M ∈ E'} (3^m/M) P(X_m ≡ M) + O((log x)^{-δ₀})`; the main
term does not depend on `Y`. -/
theorem transfer_scalar (hJM : JointMixing) (ϰ : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ d : ℝ, IrrMeasure d ϰ → ∃ C x₀ : ℝ, ∀ x Y : ℝ, x₀ ≤ x →
      x ^ alpha ≤ Y → Y ≤ x ^ (alpha ^ 2) → ∀ E : Finset ℕ, (↑E : Set ℕ) ⊆ Mset x →
        |eventProb x Y E - 2 / c * ∑ M ∈ E, (3 : ℝ) ^ mT x / M * probXm (mT x) M| ≤
          C * Lx x ^ (-δ₀) := by
  obtain ⟨δ, hδ, hR⟩ := twisted_renewal ϰ
  refine ⟨min (0.8 * δ) 1, lt_min (by positivity) one_pos, fun d hθ => ?_⟩
  obtain ⟨CR, hCR⟩ := hR d hθ 0 0 1
  set CR' := max CR 0 with hCR'
  have hCR0 : 0 ≤ CR' := le_max_right _ _
  have hCRz : ∀ u, 2 ≤ u → ‖renewalR 0 0 0 u - (1 / c : ℂ)‖ ≤ CR' * u ^ (-δ) := by
    intro u hu
    have h := hCR u 0 hu (by simp)
    simp only [mul_zero, zero_mul, add_zero, Complex.ofReal_zero, neg_zero, sub_zero,
      Complex.exp_zero, mul_one, zero_div, zero_pow two_ne_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨BR, hBR⟩ := renewalR_bounded
  set B := max BR 0 with hBdef
  have hB : ∀ u, ‖renewalR 0 0 0 u‖ ≤ B := fun u => (hBR 0 0 0 u).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  obtain ⟨CT, x₁, hT⟩ := transfer hJM 0 0 1 one_pos
  have hc := c_pos'
  set C := CT + 20 * CR' + 40 * (B + 1 / c) + 60 / c + 20 / c with hC
  have f1 := ev_of_log (ev_pow_mul_exp_le 0 1 (k := 1 / 2) (b := 0.2) (by norm_num) (by norm_num))
  have hev := large_ev.and (large2_ev.and (f1.and (eventually_ge_atTop x₁)))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hev
  refine ⟨max C 0, x₀, fun x Y hx hY1 hY2 E hE => ?_⟩
  obtain ⟨hL, hL2, g1, hx1⟩ := hx₀ x hx
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hmain := scalar_error hL hL2 hY1 hY2 E hE B CR' δ hB hCR0 hδ hCRz
  have hTx := hT x Y hx1 hY1 hY2 E hE (fun _ => 0) 0
  refine hmain.trans ?_
  set L := Lx x with hLdef
  have hLb : (200000 : ℝ) ≤ L := hL.L_ge
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set δ₀ := min (0.8 * δ) 1 with hδ₀
  -- comparison of powers
  have hp1 : L ^ (-(1 : ℝ)) ≤ L ^ (-δ₀) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_right (0.8 * δ) 1])
  have hp2 : L ^ (-(0.8 * δ)) ≤ L ^ (-δ₀) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [min_le_left (0.8 * δ) 1])
  have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
  -- the Chernoff term
  have hch : chern (mT x) (L ^ (0.6 : ℝ)) ≤ 2 * L ^ (-(1 : ℝ)) := by
    have hmn : (mT x : ℝ) ≤ n0 x := by exact_mod_cast (show mT x ≤ n0 x by
      have := two_m_le_n0 hL; omega)
    have h6 := hL2.n6
    rw [← hLdef] at h6
    refine (chern_L06_le hL0 hL2.l04 hL.m_ge (by linarith)).trans ?_
    rw [Real.rpow_zero, one_mul] at g1
    have : Real.exp (-(1 / 2 * L ^ (0.2 : ℝ))) ≤ L ^ (-(1 : ℝ)) := g1
    linarith
  have hY : L ≤ Y := by
    have h := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at h
    have : L = Real.log x := rfl
    linarith
  have h60 : 60 / (c * Y) ≤ 60 / c * L ^ (-(1 : ℝ)) := by
    rw [hLinv, div_mul_div_comm, mul_one]
    gcongr
  have hp0 : 0 ≤ L ^ (-δ₀) := Real.rpow_nonneg hL0.le _
  have hp10 : 0 ≤ L ^ (-(1 : ℝ)) := Real.rpow_nonneg hL0.le _
  have hT1 : ‖transferLHS x Y E (fun _ => 0) 0 0 0 - transferRHS x Y E (fun _ => 0) 0 0 0‖ ≤
      CT * L ^ (-δ₀) := by
    have hCT : 0 ≤ CT := by
      have := (norm_nonneg _).trans hTx
      exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos hL0 _)
    calc _ ≤ CT * L ^ (-(1 : ℝ)) := hTx
      _ ≤ CT * L ^ (-δ₀) := by gcongr
  have hcl : 0 ≤ 1 / c := by positivity
  calc _ ≤ CT * L ^ (-δ₀) + 20 * (CR' * L ^ (-δ₀) + (B + 1 / c) * (2 * L ^ (-δ₀))) +
        60 / c * L ^ (-δ₀) + 10 / c * (2 * L ^ (-δ₀)) := by
        gcongr
        · exact hch.trans (by linarith)
        · exact h60.trans (by gcongr)
        · exact hch.trans (by linarith)
    _ = C * L ^ (-δ₀) := by rw [hC]; ring
    _ ≤ max C 0 * L ^ (-δ₀) := by gcongr; exact le_max_left _ _

end CollatzCLT
