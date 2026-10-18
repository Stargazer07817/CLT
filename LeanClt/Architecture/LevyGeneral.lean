import LeanClt.Architecture.Levy

/-!
# Lévy's continuity theorem for general families of finite samples

`cltOn_of_charFun` (`Architecture/Levy.lean`) handles real statistics on the windows `A ∩ [1, X]`.
Theorem 1.1(iv) [`thm:main`] needs vector statistics, and the closing sentence of Theorem 1.1 needs
samples other than windows (`A ∩ [X, 2X]`). This file gives the same conversion for any family of
finite samples `W k` and any statistic with values in a finite-dimensional real inner product space
`E`: if the empirical characteristic functions converge to that of a probability measure `μ₀`, then
the empirical probability of every Borel set whose frontier is `μ₀`-null converges.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Finset
open scoped ENNReal NNReal

namespace CollatzCLT

variable {E : Type*} [MeasurableSpace E]

/-- The empirical law of `f` on a finite set `S`: `(1/|S|) Σ_{n∈S} δ_{f n}`. -/
noncomputable def empLawE (S : Finset ℕ) (f : ℕ → E) : Measure E :=
  ((S.card : ℝ≥0∞)⁻¹) • ∑ n ∈ S, Measure.dirac (f n)

open Classical in
lemma empLawE_apply (S : Finset ℕ) (f : ℕ → E) {B : Set E} (hB : MeasurableSet B) :
    empLawE S f B = (S.card : ℝ≥0∞)⁻¹ * ((S.filter (fun n => f n ∈ B)).card : ℝ≥0∞) := by
  simp only [empLawE, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hB, smul_eq_mul]
  congr 1
  rw [Finset.card_filter]
  push_cast
  apply sum_congr rfl
  intro n _
  by_cases h : f n ∈ B <;> simp [h]

lemma empLawE_isProb {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → E) :
    IsProbabilityMeasure (empLawE S f) := by
  constructor
  rw [empLawE_apply S f MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.inv_mul_cancel (by simpa using hS.ne_empty) (by simp)

lemma charFun_empLawE [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
    (S : Finset ℕ) (f : ℕ → E) (t : E) :
    charFun (empLawE S f) t = (S.card : ℂ)⁻¹ * ∑ n ∈ S, cexp (inner ℝ (f n) t * I) := by
  rw [charFun_apply, empLawE, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, Complex.real_smul]
  · intro n _
    exact integrable_dirac (by simp)

open Classical in
/-- **Lévy step for general samples and vector statistics.** If, along the finite samples `W k`,
the empirical characteristic functions of `S k ·` converge to that of `μ₀`, then for every Borel
set `B` with `μ₀(∂B) = 0` the proportion of `n ∈ W k` with `S k n ∈ B` tends to `μ₀(B)`. -/
theorem tendsto_propn_of_charFun [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [BorelSpace E] {W : ℕ → Finset ℕ} {S : ℕ → ℕ → E}
    (μ₀ : ProbabilityMeasure E) (hne : ∀ᶠ k in atTop, (W k).Nonempty)
    (hcf : ∀ t : E, Tendsto (fun k : ℕ => ((W k).card : ℂ)⁻¹ *
      ∑ n ∈ W k, cexp (inner ℝ (S k n) t * I)) atTop (𝓝 (charFun (μ₀ : Measure E) t)))
    {B : Set E} (hB : MeasurableSet B) (hfr : (μ₀ : Measure E) (frontier B) = 0) :
    Tendsto (fun k : ℕ => (((W k).filter (fun n => S k n ∈ B)).card : ℝ) / (W k).card) atTop
      (𝓝 ((μ₀ : Measure E).real B)) := by
  classical
  let μX : ℕ → ProbabilityMeasure E := fun k =>
    if h : (W k).Nonempty then ⟨empLawE (W k) (S k), empLawE_isProb h _⟩
    else ⟨Measure.dirac 0, inferInstance⟩
  have hμX : ∀ᶠ k in atTop, (μX k : Measure E) = empLawE (W k) (S k) := by
    filter_upwards [hne] with k hk
    simp [μX, hk]
  have hconv : Tendsto μX atTop (𝓝 μ₀) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    refine (hcf t).congr' ?_
    filter_upwards [hμX] with k hk
    rw [hk, charFun_empLawE]
  have hnull : μ₀ (frontier B) = 0 := by
    change ((μ₀ : Measure E) (frontier B)).toNNReal = 0
    rw [hfr, ENNReal.toNNReal_zero]
  have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hconv hnull
  have hlimR : Tendsto (fun k => ((μX k B : ℝ≥0) : ℝ)) atTop (𝓝 ((μ₀ B : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp hlim
  have hval : ((μ₀ B : ℝ≥0) : ℝ) = (μ₀ : Measure E).real B := by
    rw [ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.coe_toNNReal_eq_toReal]
  rw [hval] at hlimR
  refine hlimR.congr' ?_
  filter_upwards [hμX] with k hk
  have := empLawE_apply (W k) (S k) hB
  rw [ProbabilityMeasure.coeFn_def]
  simp only [hk, this, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]

end CollatzCLT
