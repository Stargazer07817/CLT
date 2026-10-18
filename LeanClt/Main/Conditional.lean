import LeanClt.Sampling.Lemma64
import LeanClt.Architecture.Levy
import LeanClt.Elementary.Flow

/-!
# Theorem 1.1 (i)–(iii), conditional on Lemma 6.1 and on positivity

The logical skeleton of §6, assembled. For each clock the paper's argument has two
non-elementary inputs, kept here as explicit hypotheses:

* `AdjacentScales (oddCF A q κ) D α`: **Lemma 6.1** for that clock. The paper derives it
  from the transfer theorem (§5), the twisted renewal theorem (§4), the joint mixing
  estimate (§3), and through them from Tao's imports and Rhin's irrationality measure.
* positive lower density of the predecessor set: **Theorem 8.1** (Mazur).

Everything else (Proposition 6.2, Corollary 6.3 in the form combined with Lemma 6.5 for `D > 0`, the
parts of Lemma 6.5 [`lem:sampling`] used here, and the verification of the transport/doubling
structure) is proved.
-/

open Real Filter Topology Finset Complex

namespace CollatzCLT

/-- A sum over the window `A ∩ [1,X]` is the sum over `[1,X]` of the indicator. -/
lemma sum_window_eq (A : Set ℕ) (f : ℕ → ℂ) (X : ℕ) :
    ∑ n ∈ window A X, f n = ∑ n ∈ Icc 1 X, A.indicator f n := by
  classical
  unfold window
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  simp [Set.indicator_apply]

/-- At frequency `0` the phase sum counts the window. -/
lemma sum_ph_zero (A : Set ℕ) (q : ℕ → ℝ) (κ : ℝ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, ph A q 0 (κ * Real.log n) n = ((window A X).card : ℂ) := by
  have : ∀ n : ℕ, ph A q 0 (κ * Real.log n) n = A.indicator (fun _ => (1 : ℂ)) n := by
    intro n; unfold ph; congr 1; ext m; simp
  simp_rw [this, ← sum_window_eq]
  simp

/-- **Final step (Corollary 6.3 for sampling from `A ∩ [1, X]`, with Lemma 6.5 [`lem:sampling`](i)).**
If the uniform-sampling phase averages converge to `e^{-D τ²} m` along every `s_X` with
`s_X √(log X) → τ`, and `A` has positive lower density, then `A` has a positive natural density
(frequency `0`) and the normalised clock `-(q(n) + κ log n)/√(2D log X)` satisfies the CLT under
uniform sampling from `A ∩ [1,X]`. The hypothesis is already centred at `κ log n`
(`uniform_limit`), so the replacement of Lemma 6.5(iii) is not used here. -/
theorem density_clt_of_uniform {A : Set ℕ} {q : ℕ → ℝ} {κ D : ℝ} (hD : 0 < D) {m : ℂ}
    (hU : ∀ (sX : ℕ → ℝ) (τ : ℝ), Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ) →
      Tendsto (fun X : ℕ => (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q (sX X) (κ * Real.log n) n) atTop
        (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * m)))
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ)) :
    (∃ d > 0, HasDensity A d) ∧
      CLTOn A (fun X n => -(q n + κ * Real.log n) / √(2 * D * Real.log X)) := by
  obtain ⟨c0, hc0, hc⟩ := hpos
  -- the density: frequency `0`
  have h0 := hU (fun _ => 0) 0 (by simp)
  simp only [sum_ph_zero, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    zero_pow two_ne_zero] at h0
  have hdC : Tendsto (fun X : ℕ => ((((window A X).card : ℝ) / X : ℝ) : ℂ)) atTop (𝓝 m) := by
    refine h0.congr' (Eventually.of_forall fun X => ?_)
    push_cast; ring
  have hdR : Tendsto (fun X : ℕ => ((window A X).card : ℝ) / X) atTop (𝓝 m.re) := by
    have := (Complex.continuous_re.tendsto _).comp hdC
    simpa [Function.comp_def] using this
  have hmim : m.im = 0 := by
    have := (Complex.continuous_im.tendsto _).comp hdC
    simp only [Function.comp_def, Complex.ofReal_im] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hm : m = (m.re : ℂ) := Complex.ext rfl (by simp [hmim])
  have hd : c0 ≤ m.re := by
    refine ge_of_tendsto hdR ?_
    filter_upwards [hc, eventually_gt_atTop 0] with X hX hX0
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
    rw [le_div_iff₀ hXpos]; exact hX
  have hdpos : 0 < m.re := lt_of_lt_of_le hc0 hd
  refine ⟨⟨m.re, hdpos, hdR⟩, ?_⟩
  -- the window is eventually nonempty
  have hne : ∀ᶠ X : ℕ in atTop, (window A X).Nonempty := by
    filter_upwards [hc, eventually_gt_atTop 0] with X hX hX0
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX0
    rw [← Finset.card_pos]
    exact_mod_cast (lt_of_lt_of_le (by positivity) hX : (0 : ℝ) < (window A X).card)
  apply cltOn_of_charFun hne
  intro t
  -- the frequency `s_X = -t / √(2D log X)`, with `s_X √(log X) → -t/√(2D)`
  set τ : ℝ := -t / √(2 * D)
  have hτ : Tendsto (fun X : ℕ => (-t / √(2 * D * Real.log X)) * √(Real.log X)) atTop (𝓝 τ) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with X hX
    have hL : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
    rw [Real.sqrt_mul (by positivity), div_mul_eq_mul_div, mul_div_mul_right _ _
      (Real.sqrt_pos.mpr hL).ne']
  have hlim := hU _ τ hτ
  have hτ2 : D * τ ^ 2 = t ^ 2 / 2 := by
    simp only [τ, div_pow, neg_sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * D)]
    field_simp
  rw [hτ2] at hlim
  -- `X / #window → 1 / m`
  have hinv : Tendsto (fun X : ℕ => (((X : ℝ) / (window A X).card : ℝ) : ℂ)) atTop
      (𝓝 ((m.re⁻¹ : ℝ) : ℂ)) := by
    apply (Complex.continuous_ofReal.tendsto _).comp
    refine ((hdR.inv₀ hdpos.ne')).congr' (Eventually.of_forall fun X => ?_)
    simp [inv_div]
  have hfinal := hinv.mul hlim
  have hval : ((m.re⁻¹ : ℝ) : ℂ) * ((Real.exp (-(t ^ 2 / 2)) : ℂ) * m) = cexp (-((t : ℂ) ^ 2 / 2)) := by
    rw [hm]
    simp only [Complex.ofReal_re]
    have : (m.re : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [Complex.ofReal_exp]; push_cast
    field_simp
  rw [hval] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [hne, eventually_gt_atTop 0] with X hX hX0
  have hcard : ((window A X).card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hX).ne'
  have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
  rw [sum_window_eq]
  have hterm : ∀ n, A.indicator (fun n => cexp ((t : ℂ) *
      ((-(q n + κ * Real.log n) / √(2 * D * Real.log X) : ℝ) : ℂ) * I)) n =
      ph A q (-t / √(2 * D * Real.log X)) (κ * Real.log n) n := by
    intro n; unfold ph
    by_cases h : n ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; congr 1; push_cast; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  simp_rw [hterm]
  push_cast
  field_simp

/-- **Uniform sampling for odd-only sets.** If `A` consists of odd integers, the phase average
over `[1, X]` tends to `e^{-D τ²} p / 2`: only the layer `e = 0` contributes. -/
theorem uniform_limit_odd {A : Set ℕ} {q : ℕ → ℝ} {κ D : ℝ} {p : ℂ} (hseq : SeqLimit A q κ D p)
    (hodd : ∀ n ∈ A, Odd n) {sX : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ)) :
    Tendsto (fun X : ℕ => (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q (sX X) (κ * Real.log n) n) atTop
      (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * (p / 2))) := by
  classical
  have hT := dyadic_tannery (L := atTop) (Z := fun X : ℕ => X)
    (f := fun X u => if Odd u then ph A q (sX X) (κ * Real.log u) u else 0)
    (fun X u => by split_ifs <;> simp [norm_ph_le])
    (ℓ := (Real.exp (-(D * τ ^ 2)) : ℂ) * p / 2) (fun k => by
      have := block_limit (e0 := 0) hseq 0 k ⟨0, fun u _ => by simp⟩ hτ
      simpa using this)
  rw [mul_div_assoc] at hT
  refine hT.congr' (Eventually.of_forall fun X => ?_)
  congr 1
  apply sum_congr rfl
  intro n _
  split_ifs with h
  · rfl
  · unfold ph
    rw [Set.indicator_of_notMem (fun hA => h (hodd n hA))]

/-! ## The three clocks -/

lemma c_pos : 0 < c := Real.log_pos (by norm_num)

lemma VT_pos : 0 < VT := by
  unfold VT; have := c_pos; have : 0 < Real.log 3 + Real.log 2 := by positivity
  positivity

lemma VF_pos : 0 < VF := by
  unfold VF; have := c_pos; have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  positivity

lemma VU_pos : 0 < VU := by
  unfold VU; have := c_pos; have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The raw clock is doubling compatible: `τ(2n) = τ(n) + 1` for `n ≥ b`. -/
lemma doubling_T (b : ℕ) (hb : 0 < b) :
    DoublingCompatible (Pred T b) (fun n => -(hit T b n : ℝ)) 1 := by
  refine ⟨b, fun n hn => ?_⟩
  have h2 : 2 * n ≠ b := by omega
  refine ⟨two_mul_mem_predT_iff (by omega) h2, fun hA => ?_⟩
  change -(hit T b (2 * n) : ℝ) = -(hit T b n : ℝ) - 1
  rw [hit_T_two_mul h2 hA]; push_cast; ring

/-- The shortcut clock is doubling compatible. -/
lemma doubling_F (b : ℕ) (hb : 0 < b) :
    DoublingCompatible (Pred F b) (fun n => -(hit F b n : ℝ)) 1 := by
  refine ⟨b, fun n hn => ?_⟩
  have h2 : 2 * n ≠ b := by omega
  refine ⟨two_mul_mem_predF_iff (by omega) h2, fun hA => ?_⟩
  change -(hit F b (2 * n) : ℝ) = -(hit F b n : ℝ) - 1
  rw [hit_F_two_mul h2 hA]; push_cast; ring

/-- Generic conditional theorem for a doubling-compatible clock. -/
theorem density_clt_of_adjacent {A : Set ℕ} {q : ℕ → ℝ} {κ D α e0 : ℝ} (hα : 1 < α) (hD : 0 < D)
    (hadj : AdjacentScales (oddCF A q κ) D α) (hdbl : DoublingCompatible A q e0)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window A X).card : ℝ)) :
    (∃ d > 0, HasDensity A d) ∧
      CLTOn A (fun X n => -(q n + κ * Real.log n) / √(2 * D * Real.log X)) := by
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj (fun Y => continuousAt_oddCF A q κ Y)
  exact density_clt_of_uniform hD (fun sX τ hτ =>
    uniform_limit (fun Y sY τ hY hτ' => hseq0 atTop Y sY τ hY hτ') hdbl hτ) hpos

/-- The normalised statistic matches the paper's form. -/
lemma stat_eq (τ : ℕ → ℕ) (κ V : ℝ) :
    (fun (X n : ℕ) => -(-(τ n : ℝ) + κ * Real.log n) / √(2 * (V / 2) * Real.log X)) =
      normalised τ κ V := by
  funext X n
  unfold normalised
  congr 1
  · ring
  · congr 1; ring

/-- **Theorem 1.1 (i)+(ii), raw clock, conditional on Lemma 6.1 and Theorem 8.1.** -/
theorem main_T (b : ℕ) (hb : 0 < b) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (Pred T b) (fun n => -(hit T b n : ℝ)) κT) (VT / 2) α)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred T b) d) ∧ CLTOn (Pred T b) (normalised (hit T b) κT VT) := by
  have := density_clt_of_adjacent hα (by linarith [VT_pos]) hadj (doubling_T b hb) hpos
  rwa [stat_eq] at this

/-- **Theorem 1.1 (i)+(ii), shortcut clock, conditional on Lemma 6.1 and positivity.** -/
theorem main_F (b : ℕ) (hb : 0 < b) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (Pred F b) (fun n => -(hit F b n : ℝ)) κF) (VF / 2) α)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred F b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred F b) d) ∧ CLTOn (Pred F b) (normalised (hit F b) κF VF) := by
  have := density_clt_of_adjacent hα (by linarith [VF_pos]) hadj (doubling_F b hb) hpos
  rwa [stat_eq] at this

/-- **Theorem 1.1 (iii), odd clock, conditional on Lemma 6.1 and positivity.** -/
theorem main_U (b : ℕ) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (PredU b) (fun n => -(hit U b n : ℝ)) κU) (VU / 2) α)
    (hpos : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (PredU b) X).card : ℝ)) :
    (∃ d > 0, HasDensity (PredU b) d) ∧ CLTOn (PredU b) (normalised (hit U b) κU VU) := by
  obtain ⟨p, -, hseq0⟩ := fixed_base_limit_seq hα hadj
    (fun Y => continuousAt_oddCF (PredU b) _ κU Y)
  have := density_clt_of_uniform (by linarith [VU_pos]) (fun sX τ hτ =>
    uniform_limit_odd (fun Y sY τ hY hτ' => hseq0 atTop Y sY τ hY hτ')
      (fun n hn => hn.2.1) hτ) hpos
  rwa [stat_eq] at this

/-- Windows are monotone in the set. -/
lemma card_window_mono {A B : Set ℕ} (h : A ⊆ B) (X : ℕ) :
    (window A X).card ≤ (window B X).card := by
  classical
  unfold window
  apply card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

/-- **Theorem 1.1 (i)+(ii), shortcut clock**, with positivity taken for the *raw* predecessor
set `P_T(2b)`, as in the paper's proof (`P_T(2b) ⊆ P_F(b)`). -/
theorem main_F' (b : ℕ) (hb : 0 < b) {α : ℝ} (hα : 1 < α)
    (hadj : AdjacentScales (oddCF (Pred F b) (fun n => -(hit F b n : ℝ)) κF) (VF / 2) α)
    (hposT : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T (2 * b)) X).card : ℝ)) :
    (∃ d > 0, HasDensity (Pred F b) d) ∧ CLTOn (Pred F b) (normalised (hit F b) κF VF) := by
  obtain ⟨c0, hc0, hc⟩ := hposT
  refine main_F b hb hα hadj ⟨c0, hc0, ?_⟩
  filter_upwards [hc] with X hX
  exact hX.trans (by exact_mod_cast card_window_mono (predT_two_mul_subset_predF b) X)

end CollatzCLT
