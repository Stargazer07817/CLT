import LeanClt.Renewal.Kernel
import LeanClt.Renewal.RotationMain

/-!
# §4.3: Abel summation against the rotation

* `abel_identity`: `∑_{j=1}^N w_j y_j = w_N D_N - ∑_{j<N} (w_{j+1} - w_j) D_j`, with
  `D_n = ∑_{j=1}^n y_j`.
* `abel_bound`: if `‖D_n‖ ≤ B` for `n ≤ N`, then
  `‖∑ w_j y_j‖ ≤ B (‖w_N‖ + ∑_{j<N} ‖w_{j+1} - w_j‖)`.
* `rotation_abel`: under Rhin's measure, with `ε = 1/(ϰ+1)` and `|v| ≤ 1`,
  `‖∑_{j=1}^N w_j (q_v(γ + jθ) - m_v)‖ ≤ C N^{1-ε} (‖w_N‖ + ∑_{j<N} ‖w_{j+1} - w_j‖)`.
-/

open Real Finset Complex

namespace CollatzCLT

lemma abel_identity (w y : ℕ → ℂ) (N : ℕ) :
    ∑ j ∈ Icc 1 N, w j * y j = w N * (∑ i ∈ Icc 1 N, y i) -
      ∑ j ∈ range N, (w (j + 1) - w j) * (∑ i ∈ Icc 1 j, y i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ,
      Finset.sum_Icc_succ_top (by omega)]
    ring

lemma abel_bound (w y : ℕ → ℂ) (N : ℕ) {B : ℝ} (hD : ∀ n ≤ N, ‖∑ i ∈ Icc 1 n, y i‖ ≤ B) :
    ‖∑ j ∈ Icc 1 N, w j * y j‖ ≤ B * (‖w N‖ + ∑ j ∈ range N, ‖w (j + 1) - w j‖) := by
  rw [abel_identity]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hD 0 (Nat.zero_le _))
  calc _ ≤ ‖w N * (∑ i ∈ Icc 1 N, y i)‖ +
        ‖∑ j ∈ range N, (w (j + 1) - w j) * (∑ i ∈ Icc 1 j, y i)‖ := norm_sub_le _ _
    _ ≤ ‖w N‖ * B + ∑ j ∈ range N, ‖w (j + 1) - w j‖ * B := by
        gcongr
        · rw [norm_mul]; gcongr; exact hD N le_rfl
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [norm_mul]; gcongr
          exact hD j (Finset.mem_range.mp hj).le
    _ = B * (‖w N‖ + ∑ j ∈ range N, ‖w (j + 1) - w j‖) := by rw [← Finset.sum_mul]; ring

/-- **Abel summation against the rotation.** -/
theorem rotation_abel {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ), |v| ≤ 1 → ∀ (γ : ℝ) (w : ℕ → ℂ) (N : ℕ),
      ‖∑ j ∈ Icc 1 N, w j * (qv v (γ + j * θ) - mv v)‖ ≤
        C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) *
          (‖w N‖ + ∑ j ∈ range N, ‖w (j + 1) - w j‖) := by
  obtain ⟨C, hC⟩ := rotation_discrepancy hθ
  have hϰ : 1 ≤ ϰ := hθ.2.1
  have hexp : 0 ≤ 1 - 1 / (ϰ + 1) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  -- `C ≥ 0` from the bound at `q = 1`
  have hC0 : 0 ≤ C := by
    have h := hC (fun _ => (1 : ℂ)) 1 0 0 (fun _ => rfl) (fun _ => by simp)
      (fun _ _ _ _ _ _ => by simp) 0 1 le_rfl
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one,
      intervalIntegral.integral_const, sub_zero, one_smul, sub_self, norm_zero,
      Real.one_rpow, add_zero, mul_one] at h
    have : (0 : ℝ) ≤ C * 1 := by simpa using h
    linarith
  refine ⟨44 * C, by positivity, fun v hv γ w N => ?_⟩
  have hq := piecewiseLip_qv hv
  have hD : ∀ n ≤ N, ‖∑ i ∈ Icc 1 n, (qv v (γ + i * θ) - mv v)‖ ≤
      44 * C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, norm_zero]
      positivity
    have h := hC (fun x => qv v x - mv v) 4 40 0 hq.per hq.bdd hq.lip γ n hpos
    rw [integral_qv_sub_mv hv, mul_zero, sub_zero] at h
    refine h.trans ?_
    have : (n : ℝ) ^ (1 - 1 / (ϰ + 1)) ≤ (N : ℝ) ^ (1 - 1 / (ϰ + 1)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) hexp
    calc C * (4 + 40) * (n : ℝ) ^ (1 - 1 / (ϰ + 1))
        ≤ C * (4 + 40) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by gcongr
      _ = 44 * C * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by ring
  exact abel_bound w (fun j => qv v (γ + j * θ) - mv v) N hD

end CollatzCLT
