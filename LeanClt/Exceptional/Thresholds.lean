import LeanClt.Transfer.AdjacentUniform
import LeanClt.Exceptional.Orbits
import LeanClt.Exceptional.Laws
import LeanClt.Positivity.Main

/-!
# Theorem 1.3 [`thm:thresholds`]: thresholds and the census of merging classes

The proof follows §6.6 of the paper, with two changes recorded in checkpoint 11.

* **(i)** For every `K`, `A_K` with the clock `-τ_K` and reward `(1, 1)` has the transport property
  at every threshold `x ≥ K` (`transport_AK`) and is doubling compatible (`doubling_AK`), so
  `density_near_base` gives the density `h_K` together with the uniform chain bound from any base
  `B ≥ max(x₁, K)^α`. At the base `B = K^α` the odd proportion of `A_K` is at least
  `1 - (log K)^{-1}` (`AK_base`, from Lemmas 5.1 and 5.2); the paper uses Lemma 5.3
  [`lem:failure`] here, whose power saving is not needed. This gives
  `h_K ≥ 1 - (1 + C)(log K)^{-δ₀}` for large `K`, and the bounded range of `K` is absorbed into the
  constant because `h_K ≥ 0`.
* **(ii)** For large `K` the bound of (i) makes `h_K > 0`, and the conditional CLT
  (`density_clt_of_adjacent`, with Lemma 6.1 for `A_K`) applies. No positivity input from §8 is used.
* **(iii)** Every merging class has the transport property with the zero clock (`transport_class`),
  so `density_near_base` gives its density; positivity comes from a predecessor set `P_T(b)` inside
  the class with `3 ∤ b` (Theorem 1.1(i), via Theorem 8.1 [`thm:positivity`]). For the census,
  the classes meeting `[1, K]` cover `A_K`, so their densities add up to at least `h_K → 1`, and
  finite sums of densities of disjoint classes are at most `1`.

This file does not import `LeanClt/Statements.lean`, so that the corollaries can later be stated
there (checkpoint 12); Theorem 1.1(i) is taken from `main_T_of_tao` and
`Positivity.positivity_of_tao` directly.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- Distinct merging classes are disjoint. -/
lemma classSet_disjoint :
    Pairwise fun C C' : Quotient mergeSetoid => Disjoint (classSet C) (classSet C') := by
  intro C C' hCC'
  rw [Set.disjoint_left]
  rintro m ⟨_, hm⟩ ⟨_, hm'⟩
  exact hCC' (hm.symm.trans hm')

/-- `log K ≥ 1` for `K ≥ 3`. -/
lemma one_le_log_of_three_le {K : ℕ} (hK : 3 ≤ K) : 1 ≤ Real.log K := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

/-- **Theorem 1.3(i).** For every `K ≥ 1` the density of `A_K` exists, and
`dens(A_K) ≥ 1 - C (log K)^{-δ₀}` for all `K ≥ 2`, with absolute `C, δ₀ > 0`. -/
theorem thresholds_i (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∀ K : ℕ, 1 ≤ K → ∃ h : ℝ, HasDensity (AK K) h) ∧
    ∃ C δ0 : ℝ, 0 < C ∧ 0 < δ0 ∧ ∀ K : ℕ, 2 ≤ K → ∀ h : ℝ, HasDensity (AK K) h →
      1 - C * (Real.log K) ^ (-δ0) ≤ h := by
  obtain ⟨δ, C, x₁, hδ, hC, hx₁, hdens⟩ := density_near_base_of_tao hTM hTP hθ 1 1
  have hK := fun K : ℕ =>
    hdens (AK K) (fun n => -(tauK K n : ℝ)) K 1 (transport_AK K) (doubling_AK K)
  refine ⟨fun K _ => let ⟨p, hp, _⟩ := hK K; ⟨p, hp⟩, ?_⟩
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (AK_base (fun _ => (0 : ℝ)) 0)
  set K₂ : ℕ := max (max K₁ ⌈x₁⌉₊) 3 with hK₂
  set δ0 := min δ 1 with hδ0def
  have hδ0 : 0 < δ0 := lt_min hδ one_pos
  set C' := max (1 + C) (Real.log K₂ ^ δ0) with hC'
  refine ⟨C', δ0, lt_of_lt_of_le (by linarith) (le_max_left _ _), hδ0, fun K hK2 h hh => ?_⟩
  obtain ⟨p, hp, hbase⟩ := hK K
  have hhp : h = p := hh.unique hp
  have hK0 : (0 : ℝ) < Real.log K := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  have hpow0 : 0 ≤ Real.log K ^ (-δ0) := Real.rpow_nonneg hK0.le _
  rw [hhp]
  by_cases hbig : K₂ ≤ K
  · -- large `K`: the base bound plus the uniform chain
    have hK1 : K₁ ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hxK : x₁ ≤ K := (Nat.le_ceil x₁).trans
      (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig)
    have hK3 : 3 ≤ K := le_trans (le_max_right _ _) hbig
    have hL1 : 1 ≤ Real.log K := one_le_log_of_three_le hK3
    have hb := hbase ((K : ℝ) ^ alpha) (by rw [max_eq_right hxK])
    have ha := hK₁ K hK1
    rw [oddCF_zero_re] at ha hb
    rw [Real.log_rpow (by positivity)] at hb
    have e1 : (alpha * Real.log K) ^ (-δ) ≤ Real.log K ^ (-δ) := by
      rw [Real.mul_rpow (by unfold alpha; norm_num) hK0.le]
      have h1 : alpha ^ (-δ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos alpha_gt_one.le (by linarith)
      have h2 : 0 ≤ Real.log K ^ (-δ) := Real.rpow_nonneg hK0.le _
      nlinarith
    have e2 : Real.log K ^ (-δ) ≤ Real.log K ^ (-δ0) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_left _ _))
    have e3 : Real.log K ^ (-(1 : ℝ)) ≤ Real.log K ^ (-δ0) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (neg_le_neg (min_le_right _ _))
    have e4 : C * (alpha * Real.log K) ^ (-δ) ≤ C * Real.log K ^ (-δ0) :=
      mul_le_mul_of_nonneg_left (e1.trans e2) hC
    have e5 : (1 + C) * Real.log K ^ (-δ0) ≤ C' * Real.log K ^ (-δ0) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0
    have hab := (abs_le.mp hb).1
    nlinarith
  · -- bounded `K`: the right side is nonpositive
    push Not at hbig
    have hL : Real.log K ≤ Real.log K₂ :=
      Real.log_le_log (by positivity) (by exact_mod_cast hbig.le)
    have h1 : Real.log K ^ δ0 ≤ Real.log K₂ ^ δ0 := Real.rpow_le_rpow hK0.le hL hδ0.le
    have h2 : Real.log K ^ δ0 * Real.log K ^ (-δ0) = 1 := by
      rw [← Real.rpow_add hK0]
      simp
    have h3 : 1 ≤ C' * Real.log K ^ (-δ0) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_right (h1.trans (le_max_right _ _)) hpow0
    linarith [hp.nonneg]

/-- **Theorem 1.3(ii).** For every sufficiently large fixed `K`, the raw clock `τ_K` satisfies the
CLT with `(κ_T, V_T)` under uniform sampling from `A_K ∩ [1, X]`. -/
theorem thresholds_ii (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → CLTOn (AK K) (normalised (tauK K) κT VT) := by
  obtain ⟨hex, C, δ0, hC, hδ0, hlow⟩ := thresholds_i hTM hTP hθ
  have hlim : Tendsto (fun K : ℕ => C * Real.log K ^ (-δ0)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hδ0).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
    simpa [Function.comp_def] using this
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    ((hlim.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 2))
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨h1, hK2⟩ := hK₀ K hK
  obtain ⟨h, hh⟩ := hex K (by omega)
  have hpos : 0 < h := by
    have := hlow K hK2 h hh
    linarith
  have hadj := adjacent_of_tao hTM hTP hθ (transport_AK K)
  have e1 : (2 * 1 + 1) / c = κT := by unfold κT; norm_num
  have e2 : (1 * bet + 1 * ell) ^ 2 / c ^ 3 = VT / 2 := by unfold VT bet ell; ring
  rw [e1, e2] at hadj
  have := density_clt_of_adjacent alpha_gt_one (by linarith [VT_pos]) hadj (doubling_AK K)
    (hh.posLower hpos)
  rw [stat_eq] at this
  exact this.2

/-- **Theorem 1.3(iii).** Every merging class has a positive density, and the densities sum to 1.
The classes are indexed by the quotient of `ℕ` by merging; the extra class of `0` has an empty
`classSet` and density `0`. -/
theorem thresholds_iii (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ dC : Quotient mergeSetoid → ℝ, (∀ C, HasDensity (classSet C) (dC C)) ∧
      (∀ n : ℕ, 0 < n → 0 < dC (Quotient.mk mergeSetoid n)) ∧ HasSum dC 1 := by
  classical
  obtain ⟨δ', C₀, x₁, -, -, -, hdens⟩ := density_near_base_of_tao hTM hTP hθ 0 0
  -- every class has a density
  have hex : ∀ C : Quotient mergeSetoid, ∃ p, HasDensity (classSet C) p := by
    intro C
    induction C using Quotient.inductionOn with
    | h n =>
      obtain ⟨p, hp, -⟩ :=
        hdens (mergeClass n) (fun _ => 0) 0 0 (transport_class n 0) (doubling_class n)
      exact ⟨p, by rw [← mergeClass_eq_classSet]; exact hp⟩
  choose dC hdC using hex
  refine ⟨dC, hdC, fun n hn => ?_, ?_⟩
  · -- positivity: a predecessor set `P_T(b)`, `3 ∤ b`, inside the class
    obtain ⟨k, hk⟩ := exists_iterate_not_three_dvd hn
    have hb : 0 < T^[k] n := iterate_T_pos hn k
    obtain ⟨⟨db, hdb, hb'⟩, -⟩ :=
      main_T_of_tao hTM hTP hθ (T^[k] n) hb (Positivity.positivity_of_tao hTM hTP hb hk)
    have hsub : Pred T (T^[k] n) ⊆ classSet (Quotient.mk mergeSetoid n) := by
      rw [← mergeClass_eq_classSet]
      intro m hm
      obtain ⟨hm0, hmb⟩ := pred_subset_mergeClass _ hm
      exact ⟨hm0, merge_equivalence.trans hmb (merge_equivalence.symm (merge_iterate n k))⟩
    exact lt_of_lt_of_le hdb (hb'.mono hsub (hdC _))
  · -- the census
    have hfin : ∀ s : Finset (Quotient mergeSetoid),
        HasDensity (⋃ C ∈ s, classSet C) (∑ C ∈ s, dC C) := fun s =>
      hasDensity_biUnion s (fun _ _ _ _ hij => classSet_disjoint hij) fun C _ => hdC C
    refine hasSum_of_isLUB_of_nonneg 1 (fun C => (hdC C).nonneg) ⟨?_, fun b hb => ?_⟩
    · rintro _ ⟨s, rfl⟩
      exact (hfin s).le_one
    · obtain ⟨hexK, C, δ0, hC, hδ0, hlow⟩ := thresholds_i hTM hTP hθ
      have hsumK : ∀ K : ℕ, 2 ≤ K → 1 - C * Real.log K ^ (-δ0) ≤ b := by
        intro K hK
        obtain ⟨h, hh⟩ := hexK K (by omega)
        -- the classes meeting `[1, K]` cover `A_K`
        have hsub : AK K ⊆ ⋃ C ∈ (Icc 1 K).image (Quotient.mk mergeSetoid), classSet C := by
          rintro n ⟨hn, k, hk⟩
          have hm0 := iterate_T_pos hn k
          simp only [Set.mem_iUnion]
          exact ⟨Quotient.mk mergeSetoid (T^[k] n),
            mem_image.mpr ⟨T^[k] n, mem_Icc.mpr ⟨hm0, hk⟩, rfl⟩, hn,
            Quotient.sound (merge_iterate n k)⟩
        exact ((hlow K hK h hh).trans (hh.mono hsub (hfin _))).trans (hb ⟨_, rfl⟩)
      have hlim : Tendsto (fun K : ℕ => 1 - C * Real.log K ^ (-δ0)) atTop (𝓝 1) := by
        have := (((tendsto_rpow_neg_atTop hδ0).comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C).const_sub 1
        simpa [Function.comp_def] using this
      exact le_of_tendsto hlim (eventually_atTop.mpr ⟨2, hsumK⟩)

end CollatzCLT
