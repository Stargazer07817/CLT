import LeanClt.Transfer.Offset

/-!
# The geometric side: bounded coefficient, restoration, smoothing (§5.4–5.5)

* `norm_Gt_le` (Lemma 5.6): `‖L_Y G̃_{r,Y}(S, z)‖ ≤ 10Y`, uniformly in `S` (the proof passes
  through `2Y H_r(z)`).
* `restore_typ`: dropping the typicality restriction on the total costs
  `10Y · P(|S_r - 2r| ≥ L^{0.6})` (Lemma 2.2(i)).
* `mix_step`: reversal (`sum_words_rev`) turns the source-order residue into `X_r`, so the word
  sum is `E_{μ_r}[L_Y G̃]`; Theorem 3.1 (`JointMixing`) replaces `μ_r` by `Q_m μ_r` at cost
  `10Y C_A m^{-A}`.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

open Classical in
/-- **Lemma 5.6 (bounded coefficient).** -/
theorem norm_Gt_le {x Y : ℝ} (hL : Large x) (hY0 : 0 ≤ Y) (E : Finset ℕ)
    (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ) (ρ η s : ℝ) {r S : ℕ} (hr : r + mT x ≤ n0 x)
    (z : ZMod (3 ^ r)) : ‖Gt Y E q ρ η s r S z‖ ≤ 10 * Y := by
  have hH := harmonic hL E hE hr z
  unfold Gt
  calc ‖∑ M ∈ E, (if (M : ZMod (3 ^ r)) = z ∧ win Y r S M then
          (2 : ℂ) ^ S * phase q ρ η s M S r else 0)‖
      ≤ ∑ M ∈ E, ‖(if (M : ZMod (3 ^ r)) = z ∧ win Y r S M then
          (2 : ℂ) ^ S * phase q ρ η s M S r else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ M ∈ E, if (M : ZMod (3 ^ r)) = z then 2 * Y * 3 ^ r * (1 / (M : ℝ)) else 0 := by
        refine Finset.sum_le_sum fun M hM => ?_
        have hM0 : (0 : ℝ) < M := by exact_mod_cast (hE hM).1.pos
        split_ifs with h1 h2 h2
        · rw [norm_mul, norm_phase, mul_one, norm_pow, Complex.norm_ofNat]
          have hw := h1.2.2
          rw [div_le_iff₀ (by positivity)] at hw
          rw [mul_one_div, le_div_iff₀ hM0]
          linarith
        · exact absurd h1.1 h2
        · rw [norm_zero]; positivity
        · rw [norm_zero]
    _ = 2 * Y * ((3 : ℝ) ^ r * ∑ M ∈ E.filter (fun M : ℕ => (M : ZMod (3 ^ r)) = z),
          (1 : ℝ) / M) := by
        rw [← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun M _ => ?_
        ring
    _ ≤ 2 * Y * 5 := by gcongr
    _ = 10 * Y := by ring

lemma sum_words_half_complex (n S : ℕ) :
    ∑ a ∈ words n S, (1 / 2 : ℝ) ^ S = lawS n S := sum_words_half n S

open Classical in
/-- **Restoring atypical totals.** -/
theorem restore_typ {x Y : ℝ} (hL : Large x) (hY0 : 0 ≤ Y) (E : Finset ℕ)
    (hE : (↑E : Set ℕ) ⊆ Mset x) (q : ℕ → ℝ) (ρ η s : ℝ) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r + mT x ≤ n0 x) (K : ℕ) :
    ‖(∑ S ∈ range (K + 1), if typT x r S then
        (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) else 0) -
      ∑ S ∈ range (K + 1),
        (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r)‖ ≤
      10 * Y * chern r (Lx x ^ (0.6 : ℝ)) := by
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ S, ‖(1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r)‖ ≤
      10 * Y * lawS r S := by
    intro S
    rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_ofNat]
    calc (1 / 2 : ℝ) ^ S * ‖∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r)‖
        ≤ (1 / 2 : ℝ) ^ S * ∑ a ∈ words r S, 10 * Y := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
            norm_Gt_le hL hY0 E hE q ρ η s hr _)
      _ = 10 * Y * ∑ a ∈ words r S, (1 / 2 : ℝ) ^ S := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
      _ = 10 * Y * lawS r S := by rw [sum_words_half]
  have hL6 : 0 ≤ Lx x ^ (0.6 : ℝ) := Real.rpow_nonneg (by linarith [hL.L_ge]) _
  calc _ ≤ ∑ S ∈ range (K + 1), ‖(if typT x r S then
        (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) else 0) -
        (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ S ∈ range (K + 1), 10 * Y *
          (if Lx x ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * r| then lawS r S else 0) := by
        refine Finset.sum_le_sum fun S _ => ?_
        by_cases hT : typT x r S
        · rw [if_pos hT, sub_self, norm_zero]
          split_ifs <;> [exact mul_nonneg (by positivity) (lawS_nonneg _ _); simp]
        · rw [if_neg hT, zero_sub, norm_neg]
          have : Lx x ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * r| := by
            unfold typT at hT; push Not at hT; exact hT.le
          rw [if_pos this]
          exact hterm S
    _ = 10 * Y * ∑ S ∈ range (K + 1),
          (if Lx x ^ (0.6 : ℝ) ≤ |(S : ℝ) - 2 * r| then lawS r S else 0) := by
        rw [Finset.mul_sum]
    _ ≤ 10 * Y * chern r (Lx x ^ (0.6 : ℝ)) := by
        gcongr
        refine le_trans ?_ (lawS_chernoff hr1 hL6)
        exact (summable_ite_lawS r _).sum_le_tsum _ (fun S _ => by
          split_ifs <;> simp [lawS_nonneg])

/-! ## The mixing step -/

lemma muJ_nonneg (n s : ℕ) (z : ZMod (3 ^ n)) : 0 ≤ muJ n s z :=
  Finset.sum_nonneg fun a _ => by split_ifs <;> positivity

lemma sum_muJ (n s : ℕ) : ∑ z : ZMod (3 ^ n), muJ n s z = lawS n s := by
  unfold muJ
  rw [Finset.sum_comm, ← sum_words_half]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

lemma Qop_nonneg (n m s : ℕ) (z : ZMod (3 ^ n)) : 0 ≤ Qop n m (muJ n) s z := by
  unfold Qop
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact muJ_nonneg _ _ _
    · exact le_rfl)

lemma Qop_le (n m s : ℕ) (hmn : m ≤ n) (z : ZMod (3 ^ n)) : Qop n m (muJ n) s z ≤ lawS n s := by
  unfold Qop
  have h1 : (3 : ℝ) ^ ((m : ℤ) - n) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have h2 : ∑ y : ZMod (3 ^ n), (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast z then
      muJ n s y else 0) ≤ lawS n s := by
    rw [← sum_muJ]
    exact Finset.sum_le_sum fun y _ => by
      split_ifs
      · exact le_rfl
      · exact muJ_nonneg _ _ _
  have h3 : 0 ≤ ∑ y : ZMod (3 ^ n), (if (ZMod.cast y : ZMod (3 ^ m)) = ZMod.cast z then
      muJ n s y else 0) := Finset.sum_nonneg fun y _ => by
    split_ifs
    · exact muJ_nonneg _ _ _
    · exact le_rfl
  calc (3 : ℝ) ^ ((m : ℤ) - n) * _ ≤ 1 * lawS n s := mul_le_mul h1 h2 h3 (by norm_num)
    _ = lawS n s := one_mul _

lemma summable_mix (n m : ℕ) (hmn : m ≤ n) :
    Summable (fun s : ℕ => ∑ z : ZMod (3 ^ n), |muJ n s z - Qop n m (muJ n) s z|) := by
  refine Summable.of_nonneg_of_le (fun s => Finset.sum_nonneg fun z _ => abs_nonneg _)
    (fun s => ?_) ((summable_lawS n).mul_left ((2 : ℝ) * ((3 ^ n : ℕ) : ℝ)))
  calc ∑ z : ZMod (3 ^ n), |muJ n s z - Qop n m (muJ n) s z|
      ≤ ∑ z : ZMod (3 ^ n), (2 * lawS n s) := Finset.sum_le_sum fun z _ => by
        have h1 := muJ_nonneg n s z
        have h2 : muJ n s z ≤ lawS n s := by
          rw [← sum_muJ]
          exact Finset.single_le_sum (fun y _ => muJ_nonneg n s y) (Finset.mem_univ z)
        have h3 := Qop_nonneg n m s z
        have h4 := Qop_le n m s hmn z
        rw [abs_le]; constructor <;> linarith
    _ = 2 * (3 ^ n : ℕ) * lawS n s := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

lemma sum_words_Xmod (r S : ℕ) (g : ZMod (3 ^ r) → ℂ) :
    (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, g (Xmod a) =
      ∑ z : ZMod (3 ^ r), (muJ r S z : ℂ) * g z := by
  rw [Finset.mul_sum, ← Finset.sum_fiberwise (words r S) (fun a => Xmod a)]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold muJ
  push_cast
  rw [Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [h]; push_cast; ring
  · simp

/-- **The smoothing step (5.11, `eq:smooth`).** -/
theorem mix_step (hJM : JointMixing) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x Y : ℝ}, Large x → 0 ≤ Y → ∀ (E : Finset ℕ), (↑E : Set ℕ) ⊆ Mset x →
      ∀ (q : ℕ → ℝ) (ρ η s : ℝ) {r : ℕ}, mT x ≤ r → r + mT x ≤ n0 x → ∀ K : ℕ,
        ‖∑ S ∈ range (K + 1),
            (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) -
          ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
            (Qop r (mT x) (muJ r) S z : ℂ) * Gt Y E q ρ η s r S z‖ ≤
        10 * Y * (C * (mT x : ℝ) ^ (-A)) := by
  obtain ⟨C, hC⟩ := hJM A hA
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x Y hL hY0 E hE q ρ η s r hmr hr K
  have hm1 := hL.m_ge
  have hJ := hC (mT x) r hm1 hmr
  have hJ' : ∑' s : ℕ, ∑ z : ZMod (3 ^ r), |muJ r s z - Qop r (mT x) (muJ r) s z| ≤
      max C 0 * (mT x : ℝ) ^ (-A) :=
    hJ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hrw : ∀ S, (1 / 2 : ℂ) ^ S * ∑ a ∈ words r S, Gt Y E q ρ η s r S (Fres (ext a) r) =
      ∑ z : ZMod (3 ^ r), (muJ r S z : ℂ) * Gt Y E q ρ η s r S z := by
    intro S
    rw [sum_words_rev r S (fun z => Gt Y E q ρ η s r S z), sum_words_Xmod]
  simp_rw [hrw]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  calc _ ≤ ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
        ‖((muJ r S z : ℂ) - (Qop r (mT x) (muJ r) S z : ℂ)) * Gt Y E q ρ η s r S z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => norm_sum_le _ _)
    _ ≤ ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
        10 * Y * |muJ r S z - Qop r (mT x) (muJ r) S z| := by
        refine Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun z _ => ?_
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_Gt_le hL hY0 E hE q ρ η s hr z) (abs_nonneg _)
    _ = 10 * Y * ∑ S ∈ range (K + 1), ∑ z : ZMod (3 ^ r),
        |muJ r S z - Qop r (mT x) (muJ r) S z| := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ 10 * Y * (max C 0 * (mT x : ℝ) ^ (-A)) := by
        gcongr
        refine le_trans ?_ hJ'
        exact (summable_mix r (mT x) hmr).sum_le_tsum _
          (fun S _ => Finset.sum_nonneg fun z _ => abs_nonneg _)

end CollatzCLT
