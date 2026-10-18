import LeanClt.Renewal.RotationMain
import LeanClt.Renewal.Abel

/-!
# Lemma 2.7 [`lem:rotation`] with `J` equally spaced jumps per period (stage 6 of the checkpoint-20 plan)

The proof of Proposition 4.5 [`prop:fixedfreq`] uses Lemma 2.7 for a `1`-periodic function with `J`
equally spaced jumps per period; v8 says the proof "extends verbatim to boundedly many jumps, with a
constant depending on Q₀", the number of jumps per period, which is `J` here. This file is that
extension, a `J`-cell copy of `Renewal/Rotation.lean`,
`RotationCount.lean` and `RotationMain.lean`. Only `IrrMeasure` is used.

* `PiecewiseLipJ q M L x₀ J`: `q` is `1`-periodic, bounded by `M`, and `L`-Lipschitz on each cell
  `(x₀ + k/J, x₀ + (k+1)/J]`; the cell of `x` is `⌈J(x - x₀)⌉`.
* `grid_sum`: `|∑_{i<K} q(c + i/K) - K ∫₀¹ q| ≤ L + 2JM`. The cell index rises by exactly `J` across
  a period, so at most `J` subintervals contain a jump.
* `card_near_jump_le`: at most `3J(2rK + 1)` grid points lie within `r` of a jump point
  `x₀ + m/J`: one `card_near_int_le` per jump of a period.
* `block_bound`: the block estimate, with the near-jump count multiplied by `J`.
* `rotation_discrepancy_jumps`: the audited statement, with `C = J(12 d^{-1/ϰ} + 14)`.
* `rotation_abel_jumps`: Abel summation against the rotation for such a `q`, the `J`-jump form of
  `rotation_abel`.
-/

open Real Finset MeasureTheory intervalIntegral

namespace CollatzCLT

/-- The hypotheses of Lemma 2.7 [`lem:rotation`] with `J` jumps per period: `1`-periodic, bounded by
`M`, `L`-Lipschitz on each cell `(x₀ + k/J, x₀ + (k+1)/J]` (the cell of `x` is `⌈J(x - x₀)⌉`). -/
structure PiecewiseLipJ (q : ℝ → ℂ) (M L x₀ : ℝ) (J : ℕ) : Prop where
  per : ∀ x, q (x + 1) = q x
  bdd : ∀ x, ‖q x‖ ≤ M
  lip : ∀ x y : ℝ, ⌈(J : ℝ) * (x - x₀)⌉ = ⌈(J : ℝ) * (y - x₀)⌉ → ‖q x - q y‖ ≤ L * |x - y|

namespace PiecewiseLipJ

variable {q : ℝ → ℂ} {M L x₀ : ℝ} {J : ℕ}

lemma periodic (hq : PiecewiseLipJ q M L x₀ J) : Function.Periodic q 1 := hq.per

lemma M_nonneg (hq : PiecewiseLipJ q M L x₀ J) : 0 ≤ M := (norm_nonneg _).trans (hq.bdd 0)

/-- The Lipschitz constant is nonnegative (a cell has distinct points). -/
lemma L_nonneg (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) : 0 ≤ L := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hc : ⌈(J : ℝ) * (x₀ + 1 / J - x₀)⌉ = ⌈(J : ℝ) * (x₀ + 1 / (2 * J) - x₀)⌉ := by
    rw [show (J : ℝ) * (x₀ + 1 / J - x₀) = 1 by rw [add_sub_cancel_left]; field_simp,
      show (J : ℝ) * (x₀ + 1 / (2 * J) - x₀) = 1 / 2 by rw [add_sub_cancel_left]; field_simp]
    norm_num
  have h := hq.lip _ _ hc
  have hd : |x₀ + 1 / J - (x₀ + 1 / (2 * J))| = 1 / (2 * J) := by
    rw [show x₀ + 1 / J - (x₀ + 1 / (2 * J)) = 1 / (2 * J) by field_simp; ring,
      abs_of_pos (by positivity)]
  rw [hd] at h
  have h0 := norm_nonneg (q (x₀ + 1 / J) - q (x₀ + 1 / (2 * J)))
  have hpos : (0 : ℝ) < 1 / (2 * J) := by positivity
  nlinarith

/-- `q` is continuous away from the jumps `x₀ + ℤ/J`. -/
lemma continuousAt (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) {x : ℝ}
    (hx : ∀ m : ℤ, (J : ℝ) * (x - x₀) ≠ m) : ContinuousAt q x := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  set k := ⌈(J : ℝ) * (x - x₀)⌉
  have h1 : (k : ℝ) - 1 < J * (x - x₀) := by
    have := Int.ceil_lt_add_one ((J : ℝ) * (x - x₀)); linarith
  have h2 : (J : ℝ) * (x - x₀) < k := lt_of_le_of_ne (Int.le_ceil _) (hx k)
  set lo := x₀ + ((k : ℝ) - 1) / J
  set hi := x₀ + (k : ℝ) / J
  have hxlo : lo < x := by
    have : ((k : ℝ) - 1) / J < x - x₀ := by rw [div_lt_iff₀ hJ0]; linarith
    simp only [lo]; linarith
  have hxhi : x < hi := by
    have : x - x₀ < (k : ℝ) / J := by rw [lt_div_iff₀ hJ0]; linarith
    simp only [hi]; linarith
  have hU : Set.Ioo lo hi ∈ nhds x := Ioo_mem_nhds hxlo hxhi
  have hcell : ∀ y ∈ Set.Ioo lo hi, ⌈(J : ℝ) * (y - x₀)⌉ = k := by
    intro y hy
    have hy1 : ((k : ℝ) - 1) / J < y - x₀ := by simp only [lo] at hy; linarith [hy.1]
    have hy2 : y - x₀ < (k : ℝ) / J := by simp only [hi] at hy; linarith [hy.2]
    rw [div_lt_iff₀ hJ0] at hy1
    rw [lt_div_iff₀ hJ0] at hy2
    rw [Int.ceil_eq_iff]
    constructor <;> nlinarith
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min r (ε / (|L| + 1)), lt_min hr (by positivity), fun y hy => ?_⟩
  have hyU : y ∈ Set.Ioo lo hi :=
    hrU (Metric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _)))
  have hxU : x ∈ Set.Ioo lo hi := ⟨hxlo, hxhi⟩
  rw [dist_eq_norm]
  have hl := hq.lip y x (by rw [hcell y hyU, hcell x hxU])
  have hd : |y - x| < ε / (|L| + 1) := by
    rw [← Real.dist_eq]; exact lt_of_lt_of_le hy (min_le_right _ _)
  calc ‖q y - q x‖ ≤ L * |y - x| := hl
    _ ≤ (|L| + 1) * |y - x| := by nlinarith [le_abs_self L, abs_nonneg (y - x)]
    _ < (|L| + 1) * (ε / (|L| + 1)) := mul_lt_mul_of_pos_left hd (by positivity)
    _ = ε := by field_simp

/-- `q` is a.e.-strongly measurable: it is continuous off the countable set `x₀ + ℤ/J`. -/
lemma aestronglyMeasurable (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) :
    AEStronglyMeasurable q volume := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
  set S := {x : ℝ | ∀ m : ℤ, (J : ℝ) * (x - x₀) ≠ m} with hSdef
  have hSc : Sᶜ ⊆ Set.range (fun m : ℤ => x₀ + (m : ℝ) / J) := by
    intro x hx
    simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    simp only
    rw [← hm]
    field_simp
    ring
  have hcount : (Sᶜ).Countable := (Set.countable_range _).mono hSc
  have hS : MeasurableSet S := hcount.measurableSet.of_compl
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ S := by
    rw [ae_iff]
    exact hcount.measure_zero volume
  have hcont : ContinuousOn q S := fun x hx => (hq.continuousAt hJ hx).continuousWithinAt
  have := hcont.aestronglyMeasurable hS (μ := volume)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- `q` is integrable on every bounded interval. -/
lemma intervalIntegrable (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) (a b : ℝ) :
    IntervalIntegrable q volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne (hq.aestronglyMeasurable hJ)
    (ae_of_all _ fun x => hq.bdd x)

/-- **Grid Riemann sums** with `J` jumps: `|∑_{i<K} q(c + i/K) - K ∫₀¹ q| ≤ L + 2JM`. -/
theorem grid_sum (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) {K : ℕ} (hK : 1 ≤ K) (c : ℝ) :
    ‖∑ i ∈ range K, q (c + i / K) - K * ∫ x in (0 : ℝ)..1, q x‖ ≤ L + 2 * J * M := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hL := hq.L_nonneg hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  set a : ℕ → ℝ := fun i => c + i / K with ha
  have hstep : ∀ i, a (i + 1) - a i = 1 / K := by intro i; simp only [ha]; push_cast; ring
  have hint : ∫ x in (0 : ℝ)..1, q x = ∑ i ∈ range K, ∫ x in a i..a (i + 1), q x := by
    rw [sum_integral_adjacent_intervals (fun k _ => hq.intervalIntegrable hJ _ _)]
    have h0 : a 0 = c := by simp [ha]
    have hKc : a K = c + 1 := by simp only [ha]; field_simp
    rw [h0, hKc]
    simpa using hq.periodic.intervalIntegral_add_eq 0 c
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
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hq.intervalIntegrable hJ _ _),
      mul_sub, ← hconst i]
  -- the cell index rises by exactly `J` across the period
  set cl : ℕ → ℤ := fun i => ⌈(J : ℝ) * (a i - x₀)⌉ with hcl
  have hmono : ∀ i, cl i ≤ cl (i + 1) := by
    intro i
    apply Int.ceil_mono
    apply mul_le_mul_of_nonneg_left _ hJ0
    linarith [hstep i, show (0 : ℝ) < 1 / K by positivity]
  have htotal : ∑ i ∈ range K, ((cl (i + 1) : ℝ) - cl i) = J := by
    rw [sum_range_sub (fun i => (cl i : ℝ))]
    have h0 : a 0 = c := by simp [ha]
    have hKc : a K = c + 1 := by simp only [ha]; field_simp
    have e : (J : ℝ) * (c + 1 - x₀) = (J : ℝ) * (c - x₀) + ((J : ℤ) : ℝ) := by push_cast; ring
    simp only [hcl, h0, hKc, e, Int.ceil_add_intCast]
    push_cast; ring
  have hterm : ∀ i ∈ range K, ‖(K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤
      L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
    intro i _
    have hlen : |a (i + 1) - a i| = 1 / K := by rw [hstep i, abs_of_pos (by positivity)]
    rw [norm_mul, Complex.norm_natCast]
    by_cases hgood : cl i = cl (i + 1)
    · have hb : ∀ t ∈ Set.uIoc (a i) (a (i + 1)), ‖q (a i) - q t‖ ≤ L / K := by
        intro t ht
        rw [Set.uIoc_of_le (by linarith [hstep i, show (0 : ℝ) < 1 / K by positivity])] at ht
        have hct : ⌈(J : ℝ) * (a i - x₀)⌉ = ⌈(J : ℝ) * (t - x₀)⌉ := by
          apply le_antisymm (Int.ceil_mono (mul_le_mul_of_nonneg_left (by linarith [ht.1]) hJ0))
          calc ⌈(J : ℝ) * (t - x₀)⌉ ≤ ⌈(J : ℝ) * (a (i + 1) - x₀)⌉ :=
                Int.ceil_mono (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hJ0)
            _ = ⌈(J : ℝ) * (a i - x₀)⌉ := hgood.symm
        calc ‖q (a i) - q t‖ ≤ L * |a i - t| := hq.lip _ _ hct
          _ ≤ L * (1 / K) := by
            gcongr
            rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.1])]
            linarith [ht.2, hstep i]
          _ = L / K := by ring
      have := norm_integral_le_of_norm_le_const hb
      rw [hlen] at this
      calc (K : ℝ) * ‖∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤ K * (L / K * (1 / K)) := by
            gcongr
        _ = L / K := by field_simp
        _ ≤ L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
            have := hq.M_nonneg
            have hd0 : (0 : ℝ) ≤ (cl (i + 1) : ℝ) - cl i := by
              have := hmono i; rw [sub_nonneg]; exact_mod_cast this
            nlinarith
    · have hd1 : (1 : ℝ) ≤ (cl (i + 1) : ℝ) - cl i := by
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
      calc (K : ℝ) * ‖∫ t in a i..a (i + 1), (q (a i) - q t)‖ ≤ K * (2 * M * (1 / K)) := by
            gcongr
        _ = 2 * M := by field_simp
        _ ≤ L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i) := by
            have := hq.M_nonneg
            have : 0 ≤ L / K := by positivity
            nlinarith
  rw [hdiff]
  calc ‖∑ i ∈ range K, (K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖
      ≤ ∑ i ∈ range K, ‖(K : ℂ) * ∫ t in a i..a (i + 1), (q (a i) - q t)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range K, (L / K + 2 * M * ((cl (i + 1) : ℝ) - cl i)) := sum_le_sum hterm
    _ = L + 2 * J * M := by
        rw [sum_add_distrib, ← mul_sum, htotal, sum_const, card_range, nsmul_eq_mul]
        field_simp

end PiecewiseLipJ

/-! ## Counting near the jumps -/

open Classical in
/-- At most `3J(2rK + 1)` of the points `c + k/K` (`k < K`) lie within `r ≤ 1/2` of `ℤ/J`. -/
lemma card_near_jump_le {J K : ℕ} (hJ : 1 ≤ J) (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hr2 : r ≤ 1 / 2) :
    (((range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - (m : ℝ) / J| ≤ r)).card : ℝ) ≤
      J * (3 * (2 * r * K + 1)) := by
  classical
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsub : (range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - (m : ℝ) / J| ≤ r) ⊆
      (range J).biUnion (fun i => (range K).filter
        (fun k : ℕ => ∃ m : ℤ, |(c - (i : ℝ) / J) + k / K - m| ≤ r)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hkK, m, hm⟩ := hk
    have hJz : (0 : ℤ) < J := by exact_mod_cast hJ
    rw [Finset.mem_biUnion]
    refine ⟨(m % J).toNat, Finset.mem_range.mpr ?_, Finset.mem_filter.mpr ⟨hkK, m / J, ?_⟩⟩
    · have := Int.emod_lt_of_pos m hJz
      have := Int.emod_nonneg m hJz.ne'
      omega
    · have h1 := Int.emod_nonneg m hJz.ne'
      have hdiv := Int.emod_add_mul_ediv m J
      have hR : ((m % J : ℤ) : ℝ) + (J : ℝ) * ((m / J : ℤ) : ℝ) = (m : ℝ) := by
        exact_mod_cast hdiv
      have hnat : (((m % J).toNat : ℕ) : ℝ) = ((m % J : ℤ) : ℝ) := by
        have := Int.toNat_of_nonneg h1
        exact_mod_cast this
      rw [hnat]
      have e : (c - ((m % J : ℤ) : ℝ) / J) + k / K - ((m / J : ℤ) : ℝ) = c + k / K - (m : ℝ) / J := by
        rw [← hR]; field_simp; ring
      rw [e]; exact hm
  calc (((range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - (m : ℝ) / J| ≤ r)).card : ℝ)
      ≤ (((range J).biUnion (fun i => (range K).filter
          (fun k : ℕ => ∃ m : ℤ, |(c - (i : ℝ) / J) + k / K - m| ≤ r))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ i ∈ range J, (((range K).filter
          (fun k : ℕ => ∃ m : ℤ, |(c - (i : ℝ) / J) + k / K - m| ≤ r)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ i ∈ range J, (3 * (2 * r * K + 1)) :=
        sum_le_sum fun i _ => card_near_int_le hK (c - (i : ℝ) / J) hr hr2
    _ = J * (3 * (2 * r * K + 1)) := by simp

/-- If `|x - y| ≤ r` and `x, y` lie in different cells, then `y - x₀` is within `r` of `ℤ/J`. -/
lemma exists_near_jump_of_ceil_ne {J : ℕ} (hJ : 1 ≤ J) {x y x₀ r : ℝ} (hxy : |x - y| ≤ r)
    (hne : ⌈(J : ℝ) * (x - x₀)⌉ ≠ ⌈(J : ℝ) * (y - x₀)⌉) : ∃ m : ℤ, |y - x₀ - (m : ℝ) / J| ≤ r := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hxy' : |(J : ℝ) * x - J * y| ≤ J * r := by
    rw [← mul_sub, abs_mul, abs_of_pos hJ0]; gcongr
  have hne' : ⌈(J : ℝ) * x - J * x₀⌉ ≠ ⌈(J : ℝ) * y - J * x₀⌉ := by
    rw [← mul_sub, ← mul_sub]; exact hne
  obtain ⟨m, hm⟩ := exists_int_near_of_ceil_ne hxy' hne'
  refine ⟨m, ?_⟩
  have e : (J : ℝ) * y - J * x₀ - m = J * (y - x₀ - (m : ℝ) / J) := by field_simp
  rw [e, abs_mul, abs_of_pos hJ0] at hm
  exact le_of_mul_le_mul_left hm hJ0

/-- `q(γ + i p / K) = q(γ + (i p mod K) / K)` for a `1`-periodic `q`. -/
lemma eq_emod_of_periodic {q : ℝ → ℂ} (hper : Function.Periodic q 1) {K : ℕ}
    (hK : 1 ≤ K) (p : ℤ) (γ : ℝ) (i : ℕ) :
    q (γ + i * ((p : ℝ) / K)) = q (γ + ((((i : ℤ) * p % K : ℤ)) : ℝ) / K) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hdiv := Int.emod_add_mul_ediv ((i : ℤ) * p) K
  have : γ + i * ((p : ℝ) / K) =
      γ + ((((i : ℤ) * p % K : ℤ)) : ℝ) / K + (((i : ℤ) * p / K : ℤ) : ℝ) * 1 := by
    have hR : (((i : ℤ) * p % K : ℤ) : ℝ) + (K : ℝ) * (((i : ℤ) * p / K : ℤ) : ℝ) =
        (i : ℝ) * p := by
      exact_mod_cast hdiv
    field_simp
    linarith
  rw [this]; exact (Function.Periodic.int_mul hper _) _

/-! ## The block estimate and the discrepancy bound -/

/-- **Block estimate with `J` jumps.** If `u p + v K = 1` and `|θ' - p/K| ≤ 1/(KQ)` with `Q ≥ 2`,
then `|∑_{i<K} q(γ + iθ') - K ∫₀¹ q| ≤ (L + 2JM) + KL/Q + 2M · J · 3(2K/Q + 1)`. -/
theorem PiecewiseLipJ.block_bound {q : ℝ → ℂ} {M L x₀ : ℝ} {J : ℕ}
    (hq : PiecewiseLipJ q M L x₀ J) (hJ : 1 ≤ J) {K : ℕ} (hK : 1 ≤ K) {p u v : ℤ}
    (huv : u * p + v * K = 1) {Q θ' : ℝ} (hQ : 2 ≤ Q) (happrox : |θ' - p / K| ≤ 1 / (K * Q))
    (γ : ℝ) :
    ‖∑ i ∈ range K, q (γ + i * θ') - K * ∫ x in (0 : ℝ)..1, q x‖ ≤
      (L + 2 * J * M) + K * L / Q + 2 * M * (J * (3 * (2 * (1 / Q) * K + 1))) := by
  classical
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hQ0 : 0 < Q := by linarith
  have hL := hq.L_nonneg hJ
  have hM := hq.M_nonneg
  have hgrid : ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K)) = ∑ k ∈ range K, q (γ + k / K) := by
    rw [sum_congr rfl fun i _ => eq_emod_of_periodic hq.periodic hK p γ i]
    have := sum_mul_emod_perm hK huv (fun j : ℤ => q (γ + (j : ℝ) / K))
    simpa using this
  set near : ℤ → ℝ := fun j =>
    if ∃ m : ℤ, |(γ - x₀) + (j : ℝ) / K - (m : ℝ) / J| ≤ 1 / Q then 1 else 0 with hnear
  have hnear_sum : ∑ i ∈ range K, near ((i : ℤ) * p % K) ≤ J * (3 * (2 * (1 / Q) * K + 1)) := by
    rw [sum_mul_emod_perm hK huv near]
    have := card_near_jump_le hJ hK (γ - x₀) (r := 1 / Q) (by positivity)
      (by rw [div_le_div_iff₀ hQ0 (by norm_num)]; linarith)
    refine le_trans (le_of_eq ?_) this
    rw [Finset.card_filter]
    push_cast
    apply sum_congr rfl
    intro k _
    simp only [hnear, Int.cast_natCast]
  have hterm : ∀ i ∈ range K, ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖ ≤
      L / Q + 2 * M * near ((i : ℤ) * p % K) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiK : (i : ℝ) ≤ K := by exact_mod_cast hi.le
    have hdist : |(γ + i * θ') - (γ + i * ((p : ℝ) / K))| ≤ 1 / Q := by
      rw [show γ + i * θ' - (γ + i * ((p : ℝ) / K)) = i * (θ' - p / K) by ring, abs_mul,
        Nat.abs_cast]
      calc (i : ℝ) * |θ' - p / K| ≤ K * (1 / (K * Q)) := by gcongr
        _ = 1 / Q := by field_simp
    have hnn : 0 ≤ near ((i : ℤ) * p % K) := by simp only [hnear]; split_ifs <;> norm_num
    by_cases hc : ⌈(J : ℝ) * ((γ + i * θ') - x₀)⌉ = ⌈(J : ℝ) * ((γ + i * ((p : ℝ) / K)) - x₀)⌉
    · calc ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖
          ≤ L * |(γ + i * θ') - (γ + i * ((p : ℝ) / K))| := hq.lip _ _ hc
        _ ≤ L * (1 / Q) := by gcongr
        _ ≤ L / Q + 2 * M * near ((i : ℤ) * p % K) := by
            rw [mul_one_div]; nlinarith
    · obtain ⟨m, hm⟩ := exists_near_jump_of_ceil_ne hJ hdist hc
      have hnear1 : near ((i : ℤ) * p % K) = 1 := by
        simp only [hnear]
        rw [ite_eq_left_iff]
        intro hP
        refine absurd ⟨m - J * ((i : ℤ) * p / K), ?_⟩ hP
        have hdiv := Int.emod_add_mul_ediv ((i : ℤ) * p) K
        have hR : (((i : ℤ) * p % K : ℤ) : ℝ) + (K : ℝ) * (((i : ℤ) * p / K : ℤ) : ℝ) =
            (i : ℝ) * p := by exact_mod_cast hdiv
        have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
        have h1 : ((m - J * ((i : ℤ) * p / K) : ℤ) : ℝ) / J =
            (m : ℝ) / J - (((i : ℤ) * p / K : ℤ) : ℝ) := by
          push_cast; field_simp
        have h2 : (((i : ℤ) * p % K : ℤ) : ℝ) / K + (((i : ℤ) * p / K : ℤ) : ℝ) =
            i * ((p : ℝ) / K) := by
          field_simp; linarith [hR]
        have e : (γ - x₀) + (((i : ℤ) * p % K : ℤ) : ℝ) / K -
            ((m - J * ((i : ℤ) * p / K) : ℤ) : ℝ) / J =
            γ + i * ((p : ℝ) / K) - x₀ - (m : ℝ) / J := by
          rw [h1]; linarith [h2]
        rw [e]; exact hm
      rw [hnear1, mul_one]
      calc ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖
          ≤ ‖q (γ + i * θ')‖ + ‖q (γ + i * ((p : ℝ) / K))‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hq.bdd _) (hq.bdd _)
        _ ≤ L / Q + 2 * M := by
            have : 0 ≤ L / Q := by positivity
            linarith
  have hsum : ‖∑ i ∈ range K, q (γ + i * θ') - ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K))‖ ≤
      K * L / Q + 2 * M * (J * (3 * (2 * (1 / Q) * K + 1))) := by
    rw [← sum_sub_distrib]
    calc ‖∑ i ∈ range K, (q (γ + i * θ') - q (γ + i * ((p : ℝ) / K)))‖
        ≤ ∑ i ∈ range K, ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range K, (L / Q + 2 * M * near ((i : ℤ) * p % K)) := sum_le_sum hterm
      _ = K * L / Q + 2 * M * ∑ i ∈ range K, near ((i : ℤ) * p % K) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ K * L / Q + 2 * M * (J * (3 * (2 * (1 / Q) * K + 1))) := by gcongr
  have hg := hq.grid_sum hJ hK γ
  rw [← hgrid] at hg
  calc ‖∑ i ∈ range K, q (γ + i * θ') - K * ∫ x in (0 : ℝ)..1, q x‖
      ≤ ‖∑ i ∈ range K, q (γ + i * θ') - ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K))‖ +
        ‖∑ i ∈ range K, q (γ + i * ((p : ℝ) / K)) - K * ∫ x in (0 : ℝ)..1, q x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K * L / Q + 2 * M * (J * (3 * (2 * (1 / Q) * K + 1)))) + (L + 2 * J * M) :=
        add_le_add hsum hg
    _ = _ := by ring

/-- The rotation discrepancy with `J` jumps, with the explicit constant `J(12 d^{-1/ϰ} + 14)`. -/
theorem rotation_discrepancy_jumps_explicit {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (J : ℕ) (hJ : 1 ≤ J)
    (q : ℝ → ℂ) (M L x₀ : ℝ) (hq : PiecewiseLipJ q M L x₀ J) (γ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * ∫ x in (0 : ℝ)..1, q x‖ ≤
      J * (12 * d ^ (-(1 / ϰ)) + 14) * (M + L) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
  obtain ⟨hd, hϰ, hrhin⟩ := hθ
  set ε : ℝ := 1 / (ϰ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε2 : ε ≤ 1 / 2 := by rw [hε, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hM := hq.M_nonneg
  have hL := hq.L_nonneg hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hdpow : 0 ≤ d ^ (-(1 / ϰ)) := Real.rpow_nonneg hd.le _
  set D := d ^ (-(1 / ϰ)) with hD
  set I := ∫ x in (0 : ℝ)..1, q x with hIdef
  set Q : ℝ := (N : ℝ) ^ (1 - ε) with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN1 (by linarith)
  have hML : 0 ≤ M + L := by linarith
  have hconst : 14 ≤ J * (12 * D + 14) := by nlinarith
  have htriv : ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * I‖ ≤ 2 * M * N := by
    have hI : ‖I‖ ≤ M := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := q) (C := M) (fun x _ => hq.bdd x)
      simpa using this
    calc ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * I‖ ≤ ‖∑ j ∈ Icc 1 N, q (γ + j * θ)‖ + ‖(N : ℂ) * I‖ :=
          norm_sub_le _ _
      _ ≤ N * M + N * M := by
          gcongr
          · calc ‖∑ j ∈ Icc 1 N, q (γ + j * θ)‖ ≤ ∑ j ∈ Icc 1 N, ‖q (γ + j * θ)‖ := norm_sum_le _ _
              _ ≤ ∑ j ∈ Icc 1 N, M := sum_le_sum fun j _ => hq.bdd _
              _ = N * M := by simp
          · rw [norm_mul, Complex.norm_natCast]; gcongr
      _ = 2 * M * N := by ring
  rcases lt_or_ge Q 2 with hQ2 | hQ2
  · have hsq : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ Q := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hN4 : (N : ℝ) < 4 := by
      have h := lt_of_le_of_lt hsq hQ2
      have : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      nlinarith [Real.rpow_nonneg hN0.le ((1 : ℝ) / 2)]
    calc _ ≤ 2 * M * N := htriv
      _ ≤ 8 * M := by nlinarith
      _ ≤ J * (12 * D + 14) * (M + L) * 1 := by nlinarith
      _ ≤ J * (12 * D + 14) * (M + L) * Q := by
          have : 0 ≤ J * (12 * D + 14) * (M + L) := by positivity
          nlinarith
  set n := ⌊Q⌋₊ with hn
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hQ2)
  obtain ⟨r, hr1, hr2⟩ := Real.exists_rat_abs_sub_le_and_den_le θ (n := n) (by omega)
  set K := r.den with hKdef
  set p := r.num with hpdef
  have hK1 : 1 ≤ K := r.den_pos
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKn : (K : ℝ) ≤ Q := le_trans (by exact_mod_cast hr2) (Nat.floor_le (by linarith))
  have hQn : Q < n + 1 := Nat.lt_floor_add_one Q
  have hrcast : (r : ℝ) = p / K := Rat.cast_def r
  have happrox : |θ - p / K| ≤ 1 / (K * Q) := by
    rw [← hrcast]
    refine hr1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨u, v, huv⟩ : IsCoprime p (K : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa using r.reduced
  have hrh := hrhin K hK1
  have hdist : distZ (K * θ) ≤ 1 / Q := by
    unfold distZ
    calc |(K : ℝ) * θ - round ((K : ℝ) * θ)| ≤ |(K : ℝ) * θ - p| := round_le _ p
      _ = K * |θ - p / K| := by
          rw [show (K : ℝ) * θ - p = K * (θ - p / K) by field_simp, abs_mul, abs_of_pos hK0]
      _ ≤ K * (1 / (K * Q)) := by gcongr
      _ = 1 / Q := by field_simp
  have hKpow : d * Q ≤ (K : ℝ) ^ ϰ := by
    have h1 : d * (K : ℝ) ^ (-ϰ) ≤ 1 / Q := hrh.trans hdist
    rw [Real.rpow_neg hK0.le] at h1
    have hKϰ : 0 < (K : ℝ) ^ ϰ := Real.rpow_pos_of_pos hK0 _
    rw [mul_inv_le_iff₀ hKϰ] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ Q)
    calc d * Q ≤ 1 / Q * (K : ℝ) ^ ϰ * Q := h2
      _ = (K : ℝ) ^ ϰ := by field_simp
  have hKlow : d ^ (1 / ϰ) * (N : ℝ) ^ ε ≤ K := by
    have hϰ0 : 0 < ϰ := by linarith
    have h1 : (d * Q) ^ (1 / ϰ) ≤ ((K : ℝ) ^ ϰ) ^ (1 / ϰ) :=
      Real.rpow_le_rpow (by positivity) hKpow (by positivity)
    rw [← Real.rpow_mul hK0.le, mul_one_div_cancel hϰ0.ne', Real.rpow_one,
      Real.mul_rpow hd.le (by positivity), hQ, ← Real.rpow_mul hN0.le] at h1
    have : (1 - ε) * (1 / ϰ) = ε := by rw [hε]; field_simp; ring
    rwa [this] at h1
  have hNK : (N : ℝ) / K ≤ D * Q := by
    have hdpos : 0 < d ^ (1 / ϰ) := Real.rpow_pos_of_pos hd _
    rw [div_le_iff₀ hK0]
    have hsplit : (N : ℝ) = (N : ℝ) ^ ε * Q := by
      rw [hQ, ← Real.rpow_add hN0]; simp
    have hinv : D * d ^ (1 / ϰ) = 1 := by
      rw [hD, ← Real.rpow_add hd]; simp
    calc (N : ℝ) = D * Q * (d ^ (1 / ϰ) * (N : ℝ) ^ ε) := by
          rw [mul_comm D Q, mul_assoc, ← mul_assoc D, hinv, one_mul, mul_comm Q, ← hsplit]
      _ ≤ D * Q * K := by gcongr
  have hNQ : (N : ℝ) / Q ≤ Q := by
    rw [div_le_iff₀ (by linarith), hQ, ← Real.rpow_add hN0]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1 - ε + (1 - ε)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  set b := N / K with hb
  set r0 := N % K with hr0
  have hNbr : N = b * K + r0 := by rw [hb, hr0, mul_comm]; exact (Nat.div_add_mod N K).symm
  have hr0K : (r0 : ℝ) ≤ K := by exact_mod_cast (Nat.mod_lt N (by omega)).le
  have hbK : (b : ℝ) ≤ N / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast Nat.div_mul_le_self N K
  set g : ℕ → ℂ := fun j => q (γ + θ + j * θ) with hg
  have hshift : ∑ j ∈ Icc 1 N, q (γ + j * θ) = ∑ j ∈ range N, g j := by
    rw [show Icc 1 N = Ico 1 (N + 1) by ext; simp, sum_Ico_eq_sum_range]
    simp only [hg, Nat.add_sub_cancel]
    apply sum_congr rfl; intro j _; congr 1; push_cast; ring
  have hdecomp : ∑ j ∈ range N, g j - N * I =
      ∑ t ∈ range b, (∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I) +
        (∑ i ∈ range r0, g (b * K + i) - r0 * I) := by
    rw [hNbr, sum_range_add, sum_range_mul_blocks, sum_sub_distrib]
    simp only [hg]
    push_cast
    have : ∀ t i : ℕ, q (γ + θ + ((t : ℝ) * K + i) * θ) = q (γ + θ + (t : ℝ) * K * θ + i * θ) := by
      intro t i; congr 1; ring
    simp_rw [this]
    rw [sum_const, card_range, nsmul_eq_mul]
    ring
  set B : ℝ := (L + 2 * J * M) + K * L / Q + 2 * M * (J * (3 * (2 * (1 / Q) * K + 1))) with hB
  have hblock : ∀ t ∈ range b,
      ‖∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I‖ ≤ B :=
    fun t _ => hq.block_bound hJ hK1 huv hQ2 happrox _
  have hrem : ‖∑ i ∈ range r0, g (b * K + i) - r0 * I‖ ≤ 2 * M * K := by
    have hI : ‖I‖ ≤ M := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := q) (C := M) (fun x _ => hq.bdd x)
      simpa using this
    calc ‖∑ i ∈ range r0, g (b * K + i) - r0 * I‖ ≤ r0 * M + r0 * M := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · calc ‖∑ i ∈ range r0, g (b * K + i)‖ ≤ ∑ i ∈ range r0, ‖g (b * K + i)‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ i ∈ range r0, M := sum_le_sum fun i _ => hq.bdd _
              _ = r0 * M := by simp
          · rw [norm_mul, Complex.norm_natCast]; gcongr
      _ ≤ 2 * M * K := by nlinarith
  rw [hshift, hdecomp]
  have hBnn : 0 ≤ B := by positivity
  calc ‖∑ t ∈ range b, (∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I) +
        (∑ i ∈ range r0, g (b * K + i) - r0 * I)‖
      ≤ ∑ t ∈ range b, B + 2 * M * K := by
        refine (norm_add_le _ _).trans
          (add_le_add ((norm_sum_le _ _).trans (sum_le_sum hblock)) hrem)
    _ = b * B + 2 * M * K := by simp
    _ ≤ (N / K) * B + 2 * M * Q := by gcongr
    _ = (N / K) * (L + 8 * J * M) + (N / Q) * (L + 12 * J * M) + 2 * M * Q := by
        rw [hB]; field_simp; ring
    _ ≤ (D * Q) * (L + 8 * J * M) + Q * (L + 12 * J * M) + 2 * M * Q := by gcongr
    _ ≤ J * (12 * D + 14) * (M + L) * Q := by
        have hQ0 : (0 : ℝ) ≤ Q := by linarith
        have hj1 : (0 : ℝ) ≤ (J : ℝ) - 1 := by linarith
        have h1 : 0 ≤ (J : ℝ) * D * M * Q := by positivity
        have h2 : 0 ≤ ((J : ℝ) - 1) * D * L * Q := by positivity
        have h3 : 0 ≤ D * L * Q := by positivity
        have h4 : 0 ≤ ((J : ℝ) - 1) * M * Q := by positivity
        have h5 : 0 ≤ ((J : ℝ) - 1) * L * Q := by positivity
        have h6 : 0 ≤ L * Q := by positivity
        have hexp : J * (12 * D + 14) * (M + L) * Q -
            ((D * Q) * (L + 8 * J * M) + Q * (L + 12 * J * M) + 2 * M * Q) =
            4 * ((J : ℝ) * D * M * Q) + 12 * (((J : ℝ) - 1) * D * L * Q) + 11 * (D * L * Q) +
              2 * (((J : ℝ) - 1) * M * Q) + 14 * (((J : ℝ) - 1) * L * Q) + 13 * (L * Q) := by
          ring
        linarith

/-- **Lemma 2.7 [`lem:rotation`] for `J` equally spaced jumps per period.** As v8 says in the
proof of Proposition 4.5 [`prop:fixedfreq`], the proof of the lemma "extends verbatim to
boundedly many jumps, with a constant depending on Q₀"; here `Q₀`, the number of jumps per
period, is `J`. `q` is `1`-periodic, bounded by `M`, and `L`-Lipschitz on each cell
`(x₀ + k/J, x₀ + (k+1)/J]` (the cell of `x` is `⌈J(x - x₀)⌉`). `C` depends on `d, ϰ, J`. -/
theorem rotation_discrepancy_jumps {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, ∀ (q : ℝ → ℂ) (M L x₀ : ℝ), (∀ x, q (x + 1) = q x) → (∀ x, ‖q x‖ ≤ M) →
      (∀ x y : ℝ, ⌈J * (x - x₀)⌉ = ⌈J * (y - x₀)⌉ → ‖q x - q y‖ ≤ L * |x - y|) →
      ∀ (γ : ℝ) (N : ℕ), 1 ≤ N →
        ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * ∫ x in (0 : ℝ)..1, q x‖ ≤
          C * (M + L) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) :=
  ⟨J * (12 * d ^ (-(1 / ϰ)) + 14), fun q M L x₀ hper hbdd hlip γ N hN =>
    rotation_discrepancy_jumps_explicit hθ J hJ q M L x₀ ⟨hper, hbdd, hlip⟩ γ N hN⟩

/-! ## Abel summation against the rotation, with `J` jumps -/

/-- **Abel summation against the rotation for a function with `J` jumps** (the `J`-jump form of
`rotation_abel`): with `ε = 1/(ϰ+1)`, `‖∑_{j=1}^N w_j (q(γ + jθ) - ∫₀¹ q)‖ ≤
C(M + L) N^{1-ε} (‖w_N‖ + ∑_{j<N} ‖w_{j+1} - w_j‖)`. `C ≥ 0` depends on `d, ϰ, J`. -/
theorem rotation_abel_jumps {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ → ℂ) (M L x₀ : ℝ), PiecewiseLipJ q M L x₀ J →
      ∀ (γ : ℝ) (w : ℕ → ℂ) (N : ℕ),
        ‖∑ j ∈ Icc 1 N, w j * (q (γ + j * θ) - ∫ x in (0 : ℝ)..1, q x)‖ ≤
          C * (M + L) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) *
            (‖w N‖ + ∑ j ∈ range N, ‖w (j + 1) - w j‖) := by
  have hd := hθ.1
  have hϰ : 1 ≤ ϰ := hθ.2.1
  have hexp : 0 ≤ 1 - 1 / (ϰ + 1) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  set C := (J : ℝ) * (12 * d ^ (-(1 / ϰ)) + 14) with hC
  have hC0 : 0 ≤ C := by have := Real.rpow_nonneg hd.le (-(1 / ϰ)); positivity
  refine ⟨C, hC0, fun q M L x₀ hq γ w N => ?_⟩
  have hML : 0 ≤ M + L := add_nonneg hq.M_nonneg (hq.L_nonneg hJ)
  set μ := ∫ x in (0 : ℝ)..1, q x
  have hD : ∀ n ≤ N, ‖∑ i ∈ Icc 1 n, (q (γ + i * θ) - μ)‖ ≤
      C * (M + L) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, norm_zero]
      positivity
    have h := rotation_discrepancy_jumps_explicit hθ J hJ q M L x₀ hq γ n hpos
    have e : ∑ i ∈ Icc 1 n, (q (γ + i * θ) - μ) = ∑ j ∈ Icc 1 n, q (γ + j * θ) - n * μ := by
      rw [sum_sub_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [e]
    refine h.trans ?_
    have : (n : ℝ) ^ (1 - 1 / (ϰ + 1)) ≤ (N : ℝ) ^ (1 - 1 / (ϰ + 1)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) hexp
    gcongr
  exact abel_bound w (fun j => q (γ + j * θ) - μ) N hD

end CollatzCLT
