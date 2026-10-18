import LeanClt.Defs

/-!
# From characteristic functions to the CLT predicate (Lévy's continuity theorem)

The paper's limit theorems are proved at the level of characteristic functions and then
converted with Lévy's continuity theorem (Corollary 6.3). This file does that conversion
for our `CLTOn` predicate. If, under uniform sampling from `A ∩ [1,X]`, the
characteristic function of `stat X N_X` converges to `e^{-t²/2}` for every `t`, then the
distribution functions converge to `Φ` at every point.

The ingredients from Mathlib are:
* Lévy's continuity theorem `ProbabilityMeasure.tendsto_of_tendsto_charFun`;
* the portmanteau theorem for sets with null boundary;
* the characteristic function of `N(0,1)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Finset
open scoped ENNReal NNReal

namespace CollatzCLT

/-- The empirical law of `f` on a finite set `S`: `(1/|S|) Σ_{n∈S} δ_{f n}`. This is the law of
`f(N)` for `N` uniform on `S`. -/
noncomputable def empLaw (S : Finset ℕ) (f : ℕ → ℝ) : Measure ℝ :=
  ((S.card : ℝ≥0∞)⁻¹) • ∑ n ∈ S, Measure.dirac (f n)

open Classical in
lemma empLaw_apply (S : Finset ℕ) (f : ℕ → ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    empLaw S f E = (S.card : ℝ≥0∞)⁻¹ * ((S.filter (fun n => f n ∈ E)).card : ℝ≥0∞) := by
  simp only [empLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hE, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply sum_congr rfl
  intro n _
  by_cases h : f n ∈ E <;> simp [h]

lemma empLaw_isProb {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    IsProbabilityMeasure (empLaw S f) := by
  constructor
  rw [empLaw_apply S f MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.inv_mul_cancel (by simpa using hS.ne_empty) (by simp)

lemma charFun_empLaw (S : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) :
    charFun (empLaw S f) t = (S.card : ℂ)⁻¹ * ∑ n ∈ S, cexp (t * f n * I) := by
  rw [charFun_apply_real, empLaw, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, Complex.real_smul]
  · intro n _
    exact integrable_dirac (by simp)

/-- **Lévy step.** If the empirical characteristic functions of `stat X ·` on `A ∩ [1,X]`
converge to `e^{-t²/2}` for every real `t`, then `CLTOn A stat` holds. -/
theorem cltOn_of_charFun {A : Set ℕ} {stat : ℕ → ℕ → ℝ}
    (hne : ∀ᶠ X in atTop, (window A X).Nonempty)
    (hcf : ∀ t : ℝ, Tendsto (fun X : ℕ => ((window A X).card : ℂ)⁻¹ *
      ∑ n ∈ window A X, cexp (t * stat X n * I)) atTop (𝓝 (cexp (-(t ^ 2 / 2))))) :
    CLTOn A stat := by
  classical
  -- the empirical laws, as probability measures (a dummy Dirac mass while the sample is empty)
  let μX : ℕ → ProbabilityMeasure ℝ := fun X =>
    if h : (window A X).Nonempty then ⟨empLaw (window A X) (stat X), empLaw_isProb h _⟩
    else ⟨Measure.dirac 0, inferInstance⟩
  let μ0 : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hμX : ∀ᶠ X in atTop, (μX X : Measure ℝ) = empLaw (window A X) (stat X) := by
    filter_upwards [hne] with X hX
    simp [μX, hX]
  -- Lévy: convergence of characteristic functions gives weak convergence
  have hconv : Tendsto μX atTop (𝓝 μ0) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    have hg : charFun (μ0 : Measure ℝ) t = cexp (-(t ^ 2 / 2)) := by
      simp only [μ0, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
      congr 1; push_cast; ring
    rw [hg]
    refine (hcf t).congr' ?_
    filter_upwards [hμX] with X hX
    rw [hX, charFun_empLaw]
  -- portmanteau: `Iic z` has null boundary for the Gaussian
  intro z
  have hnull : μ0 (frontier (Set.Iic z)) = 0 := by
    have hs : (gaussianReal 0 1 : Measure ℝ) {z} = 0 := by
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton z
    have : (μ0 : Measure ℝ) (frontier (Set.Iic z)) = 0 :=
      measure_mono_null (frontier_Iic_subset z) hs
    change ((μ0 : Measure ℝ) (frontier (Set.Iic z))).toNNReal = 0
    rw [this, ENNReal.toNNReal_zero]
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hconv hnull
  have hlimR : Tendsto (fun X => ((μX X (Set.Iic z) : ℝ≥0) : ℝ)) atTop
      (𝓝 ((μ0 (Set.Iic z) : ℝ≥0) : ℝ)) := (NNReal.continuous_coe.tendsto _).comp hlim
  have hΦ : ((μ0 (Set.Iic z) : ℝ≥0) : ℝ) = Φ z := by
    simp [Φ, μ0, cdf_eq_real, Measure.real, ENNReal.coe_toNNReal_eq_toReal]
  rw [hΦ] at hlimR
  refine hlimR.congr' ?_
  filter_upwards [hμX] with X hX
  have := empLaw_apply (window A X) (stat X) (measurableSet_Iic (a := z))
  rw [ProbabilityMeasure.coeFn_def]
  simp only [hX, this, Set.mem_Iic, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]

end CollatzCLT
