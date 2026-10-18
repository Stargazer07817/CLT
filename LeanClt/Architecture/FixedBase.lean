import LeanClt.Architecture.Chain

/-!
# Proposition 6.2 (fixed-base limit), abstract form

Here `Φ Y s` stands for `E[1_A(N_Y) e^{i s (q(N_Y) + κ log Y)}]` (§6.2), but only two
properties of it are used:

* **Lemma 6.1 (adjacent scales)**, taken as the hypothesis `AdjacentScales`: the
  renormalised function `Ψ_Y(s) = e^{D s² log Y} Φ_Y(s)` changes by at most
  `C (log Y)^{-δ}` between any two scales `Y ≤ Y' ≤ Y^α`, uniformly for
  `|s| √(log Y') ≤ M₀`;
* for each fixed `Y`, `s ↦ Φ_Y(s)` is continuous at `0`. This is true because `Φ_Y` is a
  finite average of exponentials.

**Conclusion (Proposition 6.2).** (i) `p_Y = Φ_Y(0)` converges to some `p`;
(ii) `Φ_Y(t / √log Y) → p e^{-D t²}` for every real `t`.

The proof takes the two limits in the paper's order: first `Y → ∞` with the base `B`
fixed, then `B → ∞`. No uniformity of the clock values in `Y` is needed.
-/

open Real Filter Topology

namespace CollatzCLT

/-- The renormalised characteristic function (6.3): `Ψ_Y(s) = e^{D s² log Y} Φ_Y(s)`. -/
noncomputable def renorm (Φ : ℝ → ℝ → ℂ) (D Y s : ℝ) : ℂ :=
  (Real.exp (D * s ^ 2 * Real.log Y) : ℂ) * Φ Y s

/-- **Lemma 6.1 as a hypothesis (adjacent scales).** There is `δ > 0` such that for every
`M₀ > 0` there are `C ≥ 0` and `Y₀ > 1` with
`|Ψ_Y(s) - Ψ_{Y'}(s)| ≤ C (log Y)^{-δ}` whenever `Y₀ ≤ Y ≤ Y' ≤ Y^α` and
`|s| √(log Y') ≤ M₀`. -/
def AdjacentScales (Φ : ℝ → ℝ → ℂ) (D α : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M0 : ℝ, 0 < M0 → ∃ C : ℝ, 0 ≤ C ∧ ∃ Y0 : ℝ, 1 < Y0 ∧
    ∀ Y Y' s : ℝ, Y0 ≤ Y → Y ≤ Y' → Y' ≤ Y ^ α →
    |s| * √(Real.log Y') ≤ M0 →
      ‖renorm Φ D Y s - renorm Φ D Y' s‖ ≤ C * (Real.log Y) ^ (-δ)

/-- The chain estimate (6.7, `eq:chain`) in the `Y` variable, at a fixed frequency `s` admissible at the
top scale `Y`. -/
lemma chain_Y {Φ : ℝ → ℝ → ℂ} {D α δ C Y0 M0 : ℝ} (hα : 1 < α) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hY0 : 1 < Y0)
    (h : ∀ Y Y' s : ℝ, Y0 ≤ Y → Y ≤ Y' → Y' ≤ Y ^ α → |s| * √(Real.log Y') ≤ M0 →
      ‖renorm Φ D Y s - renorm Φ D Y' s‖ ≤ C * (Real.log Y) ^ (-δ))
    {B Y s : ℝ} (hB : Y0 ≤ B) (hBY : B ≤ Y) (hs : |s| * √(Real.log Y) ≤ M0) :
    ‖renorm Φ D Y s - renorm Φ D B s‖ ≤ C / (1 - α ^ (-δ)) * (Real.log B) ^ (-δ) := by
  have hB0 : 0 < B := by linarith
  have hY0' : 0 < Y := by linarith
  set g : ℝ → ℂ := fun u => renorm Φ D (Real.exp u) s with hg
  have hadj : ∀ u u', Real.log Y0 ≤ u → u ≤ u' → u' ≤ α * u → u' ≤ Real.log Y →
      ‖g u - g u'‖ ≤ C * u ^ (-δ) := by
    intro u u' hu0 huu' hu'α hu'max
    have key := h (Real.exp u) (Real.exp u') s
      (by rw [← Real.exp_log (by linarith : (0 : ℝ) < Y0)]; exact Real.exp_le_exp.mpr hu0)
      (Real.exp_le_exp.mpr huu')
      (by rw [← Real.exp_mul]; exact Real.exp_le_exp.mpr (by linarith [mul_comm u α]))
      (by
        rw [Real.log_exp]
        calc |s| * √u' ≤ |s| * √(Real.log Y) := by
              gcongr
          _ ≤ M0 := hs)
    simpa [hg, Real.log_exp] using key
  have hb : 0 < Real.log B := Real.log_pos (by linarith)
  have := chain_bound (g := g) hα hδ hC hadj (Real.log_le_log (by linarith) hB) hb
    (Real.log_le_log hB0 hBY) le_rfl
  simpa [hg, Real.exp_log hB0, Real.exp_log hY0'] using this

/-- **Proposition 6.2 (fixed-base limit), sequential form.**
(i) `p_Y = Φ_Y(0)` converges to some `p`; and (ii') along any scales `Y_i → ∞` and
frequencies `s_i` with `s_i √(log Y_i) → τ` (indexed by an arbitrary filter),
`Φ_{Y_i}(s_i) → e^{-D τ²} p`.

The paper's (ii) is the special case `Y_i = Y`, `s_i = t/√(log Y)`, below. The sequential
form is what Lemma 6.5 [`lem:sampling`] needs. The dyadic decomposition there produces scale/frequency pairs
`(Y_X, s_X)` indexed by the outer sampling bound `X`, the normalisations `√(log Y_X)` and
`√(log X)` differ by a factor tending to `1`, and several `X` can share one scale. The
paper's proof gives this form without change, because the chain estimate is uniform in
`|s| √(log Y) ≤ M₀`. -/
theorem fixed_base_limit_seq {Φ : ℝ → ℝ → ℂ} {D α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales Φ D α) (hcont : ∀ Y, ContinuousAt (Φ Y) 0) :
    ∃ p : ℂ, Tendsto (fun Y => Φ Y 0) atTop (𝓝 p) ∧
      ∀ {ι : Type} (L : Filter ι) (Y sY : ι → ℝ) (τ : ℝ), Tendsto Y L atTop →
        Tendsto (fun i => sY i * √(Real.log (Y i))) L (𝓝 τ) →
        Tendsto (fun i => Φ (Y i) (sY i)) L (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p)) := by
  obtain ⟨δ, hδ, hM⟩ := hadj
  have hr1 : α ^ (-δ) < 1 := rpow_lt_one_of_one_lt_of_neg hα (by linarith)
  -- `(log B)^{-δ} → 0`
  have hdecay : Tendsto (fun B : ℝ => (Real.log B) ^ (-δ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop
  have hren0 : ∀ Y, renorm Φ D Y 0 = Φ Y 0 := by intro Y; simp [renorm]
  /- (i) the proportions `p_Y = Φ_Y(0)` form a Cauchy family. -/
  obtain ⟨C, hC, Y0, hY0, h⟩ := hM 1 one_pos
  have hstep0 : ∀ B Y, Y0 ≤ B → B ≤ Y →
      ‖Φ Y 0 - Φ B 0‖ ≤ C / (1 - α ^ (-δ)) * (Real.log B) ^ (-δ) := by
    intro B Y hB hBY
    have := chain_Y hα hδ hC hY0 h hB hBY (s := 0) (by simp)
    rwa [hren0, hren0] at this
  have hcs : CauchySeq (fun Y : ℝ => Φ Y 0) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := ((hdecay.const_mul (C / (1 - α ^ (-δ)))).eventually (gt_mem_nhds
      (show C / (1 - α ^ (-δ)) * 0 < ε by rw [mul_zero]; exact hε))).and
      (eventually_ge_atTop Y0)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun Y hY => ?_⟩
    rw [dist_eq_norm]
    exact (hstep0 N Y (hN N le_rfl).2 hY).trans_lt (hN N le_rfl).1
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨p, hp, ?_⟩
  /- (ii') first `i → ∞` along `L` with the base `B` fixed, then `B → ∞`. -/
  intro ι L Y sY τ hY hτ
  have hsqrt : Tendsto (fun i => √(Real.log (Y i))) L atTop :=
    (tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp hY
  -- `s_i → 0`
  have hs0 : Tendsto sY L (𝓝 0) := by
    have h1 : Tendsto (fun i => sY i * √(Real.log (Y i)) / √(Real.log (Y i))) L (𝓝 0) :=
      hτ.div_atTop hsqrt
    refine h1.congr' ?_
    filter_upwards [hY.eventually (eventually_gt_atTop 1)] with i hi
    have := Real.sqrt_pos.mpr (Real.log_pos hi)
    field_simp
  -- `|s_i| √(log Y_i)` is eventually bounded by `M₀ = |τ| + 1`
  have hbd : ∀ᶠ i in L, |sY i| * √(Real.log (Y i)) ≤ |τ| + 1 := by
    have := (continuous_abs.tendsto τ).comp hτ
    filter_upwards [this.eventually (gt_mem_nhds (by linarith : |τ| < |τ| + 1))] with i hi
    have hL := Real.sqrt_nonneg (Real.log (Y i))
    simp only [Function.comp, abs_mul, abs_of_nonneg hL] at hi
    exact hi.le
  -- the renormalised function along `(Y_i, s_i)` tends to `p`
  have hmain : Tendsto (fun i => renorm Φ D (Y i) (sY i)) L (𝓝 p) := by
    obtain ⟨C', hC', Y0', hY0', h'⟩ := hM (|τ| + 1) (by positivity)
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- choose the base `B`
    have hevB := ((hdecay.const_mul (C' / (1 - α ^ (-δ)))).eventually
      (gt_mem_nhds (show C' / (1 - α ^ (-δ)) * 0 < ε / 3 by rw [mul_zero]; positivity))).and
      (((hp.eventually (Metric.ball_mem_nhds p (by positivity : (0 : ℝ) < ε / 3)))).and
        (eventually_ge_atTop Y0'))
    obtain ⟨B, hB⟩ := eventually_atTop.mp hevB
    obtain ⟨hB1, hB2, hB3⟩ := hB B le_rfl
    -- at the fixed base, `Ψ_B(s) → Ψ_B(0) = p_B` as `s → 0`
    have hcontB : ContinuousAt (fun s => renorm Φ D B s) 0 := by
      unfold renorm
      exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul (continuous_pow 2)).mul continuous_const))).continuousAt).mul
        (hcont B)
    have hlimB : Tendsto (fun i => renorm Φ D B (sY i)) L (𝓝 (Φ B 0)) := by
      have := hcontB.tendsto.comp hs0
      rwa [hren0] at this
    filter_upwards [hlimB.eventually (Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < ε / 3)),
      hY.eventually (eventually_ge_atTop B), hbd] with i hY1a hYB hfreq
    have hchain := chain_Y hα hδ hC' hY0' h' hB3 hYB hfreq
    rw [dist_eq_norm]
    calc ‖renorm Φ D (Y i) (sY i) - p‖
        ≤ ‖renorm Φ D (Y i) (sY i) - renorm Φ D B (sY i)‖
          + ‖renorm Φ D B (sY i) - Φ B 0‖ + ‖Φ B 0 - p‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub
            (renorm Φ D (Y i) (sY i)) (renorm Φ D B (sY i)) p
          have := norm_sub_le_norm_sub_add_norm_sub (renorm Φ D B (sY i)) (Φ B 0) p
          linarith
      _ < ε / 3 + ε / 3 + ε / 3 := by
          gcongr
          · exact hchain.trans_lt hB1
          · rw [← dist_eq_norm]; exact hY1a
          · rw [← dist_eq_norm]; exact hB2
      _ = ε := by ring
  -- undo the renormalisation: `Φ_Y(s) = e^{-D (s √log Y)²} Ψ_Y(s)` for `Y > 1`
  have hfac : Tendsto (fun i => Complex.ofReal (Real.exp (-(D * (sY i * √(Real.log (Y i))) ^ 2))))
      L (𝓝 (Complex.ofReal (Real.exp (-(D * τ ^ 2))))) := by
    apply (Complex.continuous_ofReal.tendsto _).comp
    apply (Real.continuous_exp.tendsto _).comp
    exact ((hτ.pow 2).const_mul D).neg
  refine (hfac.mul hmain).congr' ?_
  filter_upwards [hY.eventually (eventually_gt_atTop 1)] with i hi
  have hL : 0 < Real.log (Y i) := Real.log_pos hi
  have hsq : D * sY i ^ 2 * Real.log (Y i) = D * (sY i * √(Real.log (Y i))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hL.le]; ring
  simp only [renorm, hsq, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp

/-- **Proposition 6.2 (fixed-base limit), as stated in the paper.** -/
theorem fixed_base_limit {Φ : ℝ → ℝ → ℂ} {D α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales Φ D α) (hcont : ∀ Y, ContinuousAt (Φ Y) 0) :
    ∃ p : ℂ, Tendsto (fun Y => Φ Y 0) atTop (𝓝 p) ∧
      ∀ t : ℝ, Tendsto (fun Y => Φ Y (t / √(Real.log Y))) atTop
        (𝓝 ((Real.exp (-(D * t ^ 2)) : ℂ) * p)) := by
  obtain ⟨p, hp, hs⟩ := fixed_base_limit_seq hα hadj hcont
  refine ⟨p, hp, fun t => hs atTop id _ t tendsto_id (tendsto_const_nhds.congr' ?_)⟩
  filter_upwards [eventually_gt_atTop 1] with Y hY
  have := Real.sqrt_pos.mpr (Real.log_pos hY)
  simp only [id]
  field_simp

end CollatzCLT
