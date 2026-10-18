import LeanClt.Renewal.Defs

/-!
# Lemma 2.7 [`lem:rotation`] (rotation discrepancy), part 1: piecewise Lipschitz periodic functions

`PiecewiseLip q M L x₀`: `q` is `1`-periodic, bounded by `M`, and `L`-Lipschitz on the period cell
`(x₀, x₀ + 1]`, so it jumps only at `x₀ + ℤ`. The cell of `x` is `⌈x - x₀⌉`.

* `cell_lip`: two points in the same cell are `L`-Lipschitz close.
* `intervalIntegrable`: `q` is integrable on every bounded interval.
* `grid_sum`: `|∑_{i<K} q(c + i/K) - K ∫₀¹ q| ≤ L + 2M` for every `c` and `K ≥ 1`. At most one
  of the `K` subintervals `[c + i/K, c + (i+1)/K]` contains a jump, because the cell index rises
  by exactly `1` across a period.
-/

open Real Finset MeasureTheory intervalIntegral

namespace CollatzCLT

/-- The hypotheses of Lemma 2.7 [`lem:rotation`]: `1`-periodic, bounded by `M`, `L`-Lipschitz on `(x₀, x₀ + 1]`. -/
structure PiecewiseLip (q : ℝ → ℂ) (M L x₀ : ℝ) : Prop where
  per : ∀ x, q (x + 1) = q x
  bdd : ∀ x, ‖q x‖ ≤ M
  lip : ∀ x y, x₀ < x → x ≤ x₀ + 1 → x₀ < y → y ≤ x₀ + 1 → ‖q x - q y‖ ≤ L * |x - y|

namespace PiecewiseLip

variable {q : ℝ → ℂ} {M L x₀ : ℝ}

lemma periodic (hq : PiecewiseLip q M L x₀) : Function.Periodic q 1 := hq.per

lemma M_nonneg (hq : PiecewiseLip q M L x₀) : 0 ≤ M := (norm_nonneg _).trans (hq.bdd 0)

/-- Two points in the same cell (`⌈x - x₀⌉ = ⌈y - x₀⌉`) are `L`-Lipschitz close. -/
lemma cell_lip (hq : PiecewiseLip q M L x₀) {x y : ℝ} (h : ⌈x - x₀⌉ = ⌈y - x₀⌉) :
    ‖q x - q y‖ ≤ L * |x - y| := by
  set k : ℤ := ⌈x - x₀⌉ - 1 with hk
  have hx1 := Int.le_ceil (x - x₀)
  have hx2 := Int.ceil_lt_add_one (x - x₀)
  have hy1 := Int.le_ceil (y - x₀)
  have hy2 := Int.ceil_lt_add_one (y - x₀)
  rw [← h] at hy1 hy2
  have hkR : (k : ℝ) = (⌈x - x₀⌉ : ℝ) - 1 := by rw [hk]; push_cast; ring
  have ex : q x = q (x - k * 1) := (hq.periodic.sub_int_mul_eq k).symm
  have ey : q y = q (y - k * 1) := (hq.periodic.sub_int_mul_eq k).symm
  rw [ex, ey]
  have := hq.lip (x - k * 1) (y - k * 1) (by rw [hkR]; linarith) (by rw [hkR]; linarith)
    (by rw [hkR]; linarith) (by rw [hkR]; linarith)
  rwa [show x - k * 1 - (y - k * 1) = x - y by ring] at this

/-- `q` is continuous away from the jumps `x₀ + ℤ`. -/
lemma continuousAt (hq : PiecewiseLip q M L x₀) {x : ℝ} (hx : ∀ m : ℤ, x - x₀ ≠ m) :
    ContinuousAt q x := by
  set k := ⌈x - x₀⌉
  have h1 : (k : ℝ) - 1 < x - x₀ := by have := Int.ceil_lt_add_one (x - x₀); linarith
  have h2 : x - x₀ < k := lt_of_le_of_ne (Int.le_ceil _) (hx k)
  -- on the open cell `(x₀ + k - 1, x₀ + k)` the cell index is constant
  have hU : Set.Ioo (x₀ + k - 1) (x₀ + k) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  have hcell : ∀ y ∈ Set.Ioo (x₀ + k - 1) (x₀ + k), ⌈y - x₀⌉ = k := by
    intro y hy
    rw [Int.ceil_eq_iff]; constructor <;> linarith [hy.1, hy.2]
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min r (ε / (|L| + 1)), lt_min hr (by positivity), fun y hy => ?_⟩
  have hyU : y ∈ Set.Ioo (x₀ + k - 1) (x₀ + k) :=
    hrU (Metric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _)))
  have hxU : x ∈ Set.Ioo (x₀ + k - 1) (x₀ + k) := ⟨by linarith, by linarith⟩
  rw [dist_eq_norm]
  have hl := hq.cell_lip (x := y) (y := x) (by rw [hcell y hyU, hcell x hxU])
  have hd : |y - x| < ε / (|L| + 1) := by
    rw [← Real.dist_eq]; exact lt_of_lt_of_le hy (min_le_right _ _)
  calc ‖q y - q x‖ ≤ L * |y - x| := hl
    _ ≤ (|L| + 1) * |y - x| := by nlinarith [le_abs_self L, abs_nonneg (y - x)]
    _ < (|L| + 1) * (ε / (|L| + 1)) := mul_lt_mul_of_pos_left hd (by positivity)
    _ = ε := by field_simp

/-- The Lipschitz constant is nonnegative (the cell has distinct points). -/
lemma L_nonneg (hq : PiecewiseLip q M L x₀) : 0 ≤ L := by
  have h := hq.lip (x₀ + 1) (x₀ + 1 / 2) (by linarith) le_rfl (by linarith) (by linarith)
  rw [show x₀ + 1 - (x₀ + 1 / 2) = 1 / 2 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  nlinarith [norm_nonneg (q (x₀ + 1) - q (x₀ + 1 / 2))]

/-- `q` is a.e.-strongly measurable: it is continuous off the countable set `x₀ + ℤ`. -/
lemma aestronglyMeasurable (hq : PiecewiseLip q M L x₀) : AEStronglyMeasurable q volume := by
  set S := {x : ℝ | ∀ m : ℤ, x - x₀ ≠ m} with hSdef
  have hSc : Sᶜ ⊆ Set.range (fun m : ℤ => x₀ + m) := by
    intro x hx
    simp only [hSdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not] at hx
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, by simp only; linarith⟩
  have hcount : (Sᶜ).Countable := (Set.countable_range _).mono hSc
  have hS : MeasurableSet S := hcount.measurableSet.of_compl
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ S := by
    rw [ae_iff]
    exact hcount.measure_zero volume
  have hcont : ContinuousOn q S := fun x hx => (hq.continuousAt hx).continuousWithinAt
  have := hcont.aestronglyMeasurable hS (μ := volume)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- `q` is integrable on every bounded interval. -/
lemma intervalIntegrable (hq : PiecewiseLip q M L x₀) (a b : ℝ) :
    IntervalIntegrable q volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne hq.aestronglyMeasurable
    (ae_of_all _ fun x => hq.bdd x)

/-- **Grid Riemann sums.** `|∑_{i<K} q(c + i/K) - K ∫₀¹ q| ≤ L + 2M`. -/
theorem grid_sum (hq : PiecewiseLip q M L x₀) {K : ℕ} (hK : 1 ≤ K) (c : ℝ) :
    ‖∑ i ∈ range K, q (c + i / K) - K * ∫ x in (0 : ℝ)..1, q x‖ ≤ L + 2 * M := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hL := hq.L_nonneg
  set a : ℕ → ℝ := fun i => c + i / K with ha
  have hstep : ∀ i, a (i + 1) - a i = 1 / K := by intro i; simp only [ha]; push_cast; ring
  -- `∫₀¹ q = ∑_i ∫_{a_i}^{a_{i+1}} q`
  have hint : ∫ x in (0 : ℝ)..1, q x = ∑ i ∈ range K, ∫ x in a i..a (i + 1), q x := by
    rw [sum_integral_adjacent_intervals (fun k _ => hq.intervalIntegrable _ _)]
    have h0 : a 0 = c := by simp [ha]
    have hKc : a K = c + 1 := by simp only [ha]; field_simp
    rw [h0, hKc]
    simpa using hq.periodic.intervalIntegral_add_eq 0 c
  -- each `q(a_i)` is `K` times the integral of the constant over its subinterval
  have hconst : ∀ i, q (a i) = K * ∫ _ in a i..a (i + 1), q (a i) := by
    intro i
    rw [intervalIntegral.integral_const, hstep i, Complex.real_smul]
    have hKc : (K : ℂ) ≠ 0 := by exact_mod_cast hK'.ne'
    push_cast; field_simp
  have hdiff : ∑ i ∈ range K, q (c + i / K) - K * ∫ x in (0 : ℝ)..1, q x =
      ∑ i ∈ range K, (K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t) := by
    rw [hint, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hq.intervalIntegrable _ _), mul_sub,
      ← hconst i]
  -- the cell index rises by exactly `1` across the period
  set cl : ℕ → ℤ := fun i => ⌈a i - x₀⌉ with hcl
  have hmono : ∀ i, cl i ≤ cl (i + 1) := by
    intro i; apply Int.ceil_mono; linarith [hstep i, show (0 : ℝ) < 1 / K by positivity]
  have htotal : ∑ i ∈ range K, ((cl (i + 1) : ℝ) - cl i) = 1 := by
    rw [sum_range_sub (fun i => (cl i : ℝ))]
    have h0 : a 0 = c := by simp [ha]
    have hKc : a K = c + 1 := by simp only [ha]; field_simp
    simp only [hcl, h0, hKc, show c + 1 - x₀ = (c - x₀) + 1 by ring, Int.ceil_add_one]
    push_cast; ring
  -- termwise bound
  have hterm : ∀ i ∈ range K, ‖(K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤
      L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
    intro i _
    have hd0 : (0 : ℝ) ≤ (cl (i + 1) : ℝ) - cl i := by
      have := hmono i; rw [sub_nonneg]; exact_mod_cast this
    have hlen : |a (i + 1) - a i| = 1 / K := by rw [hstep i, abs_of_pos (by positivity)]
    rw [norm_mul, Complex.norm_natCast]
    by_cases hgood : cl i = cl (i + 1)
    · -- no jump: Lipschitz on the whole subinterval
      have hb : ∀ t ∈ Set.uIoc (a i) (a (i + 1)), ‖q (a i) - q t‖ ≤ L / K := by
        intro t ht
        rw [Set.uIoc_of_le (by linarith [hstep i, show (0 : ℝ) < 1 / K by positivity])] at ht
        have hct : ⌈a i - x₀⌉ = ⌈t - x₀⌉ := by
          apply le_antisymm (Int.ceil_mono (by linarith [ht.1]))
          calc ⌈t - x₀⌉ ≤ ⌈a (i + 1) - x₀⌉ := Int.ceil_mono (by linarith [ht.2])
            _ = ⌈a i - x₀⌉ := hgood.symm
        calc ‖q (a i) - q t‖ ≤ L * |a i - t| := hq.cell_lip hct
          _ ≤ L * (1 / K) := by
            gcongr
            rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
            linarith [ht.2, hstep i]
          _ = L / K := by ring
      have := norm_integral_le_of_norm_le_const hb
      rw [hlen] at this
      calc (K : ℝ) * ‖∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤ K * (L / K * (1 / K)) := by gcongr
        _ = L / K := by field_simp
        _ ≤ L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
            have := hq.M_nonneg; nlinarith
    · -- a jump: bound by `2M`
      have hd1 : (1 : ℝ) ≤ (cl (i + 1) : ℝ) - cl i := by
        have : cl i < cl (i + 1) := lt_of_le_of_ne (hmono i) hgood
        have : cl i + 1 ≤ cl (i + 1) := this
        have : ((cl i : ℝ) + 1 ≤ cl (i + 1)) := by exact_mod_cast this
        linarith
      have hb : ∀ t ∈ Set.uIoc (a i) (a (i + 1)), ‖q (a i) - q t‖ ≤ 2 * M := by
        intro t _
        calc ‖q (a i) - q t‖ ≤ ‖q (a i)‖ + ‖q t‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hq.bdd _) (hq.bdd _)
          _ = 2 * M := by ring
      have := norm_integral_le_of_norm_le_const hb
      rw [hlen] at this
      calc (K : ℝ) * ‖∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤ K * (2 * M * (1 / K)) := by gcongr
        _ = 2 * M := by field_simp
        _ ≤ L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
            have := hq.M_nonneg
            have : 0 ≤ L / K := by positivity
            nlinarith
  rw [hdiff]
  calc ‖∑ i ∈ range K, (K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖
      ≤ ∑ i ∈ range K, ‖(K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range K, (L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i)) := sum_le_sum hterm
    _ = L + 2 * M := by
        rw [sum_add_distrib, ← mul_sum, htotal, sum_const, card_range, nsmul_eq_mul]
        field_simp

end PiecewiseLip

end CollatzCLT
