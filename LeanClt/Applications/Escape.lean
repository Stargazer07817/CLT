import LeanClt.Applications.AntiConc
import LeanClt.Exceptional.Rays

/-!
# Corollary 6.11 [`cor:escape`]: deterministic-time escape (stage 5 of the checkpoint-20 plan)

Under all three hypotheses (`TaoMajorant`, `TaoPrefix`, `IrrMeasure`); the Diophantine input enters
only through the class density `π_C > 0` (Theorem 1.3(iii), `thresholds_iii`), the densities of
`A_K` and their lower bound (Theorem 1.3(i), `thresholds_i`), and the existence of `dens(A_K ∩ C)`
(`density_near_base_of_tao`).

* **`F^t(N_X) ≤ K` is a union of `K` level sets** of the shortcut coordinate: on the class,
  `ℓ_C(n) = ℓ_C(F^t n) - t` (`coordF_iterate`), so `F^t(n) = m ≤ K` puts `n` in the level set
  `{ℓ_C = ℓ_C(m) - t}`, `1 ≤ m ≤ K`. Theorem 6.10(ii) bounds each by `C₀X/√(log X)`, uniformly in
  the level, and `#(C ∩ [1, X]) ≥ π_C X/2` for large `X` gives the constant `C_C = 2C₀/π_C`
  (`C₀` of Theorem 6.10; the statement's constant is `2C₀`). The threshold depends on the class
  only, not on `K` or `t`.
* **The second sentence.** `A_K` is also the set of positive `n` whose `F`-orbit reaches `[1, K]`
  (`AK_eq_F`), so the proportion is `#(A_K ∩ C ∩ [1, X])/#(C ∩ [1, X])`. The intersection has the
  transport and doubling properties (`transport_inter_class`, `doubling_inter_class`), hence a
  density `dens(A_K ∩ C)` by `density_near_base_of_tao`, and the ratio tends to `dens(A_K ∩ C)/π_C`
  (`tendsto_card_div_card`). Since `C ∖ A_K` lies in the complement of `A_K`, whose density is at most
  `C(log K)^{-δ₀}` by Theorem 1.3(i), `dens(A_K ∩ C)/π_C → 1`.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- Shortcut iterates of a positive integer are positive. -/
lemma iterate_F_pos {n : ℕ} (hn : 0 < n) (t : ℕ) : 0 < F^[t] n := by
  obtain ⟨k, hk⟩ := exists_T_iterate_eq_F_iterate n t
  rw [← hk]
  exact iterate_T_pos hn k

/-- `A_K` is also the set of positive `n` whose `F`-orbit reaches `[1, K]` (Corollary 6.11 is
stated with `F^t`). -/
lemma AK_eq_F (K : ℕ) : AK K = {n | 0 < n ∧ ∃ t, F^[t] n ≤ K} := by
  ext n
  constructor
  · rintro ⟨hn, k, hk⟩
    refine ⟨hn, ?_⟩
    obtain ⟨j, hj | ⟨hodd, hj⟩⟩ := exists_F_iterate_or_odd n k
    · exact ⟨j, hj ▸ hk⟩
    · -- the raw state is the skipped `3x + 1`, and `x` itself is a shortcut state below it
      refine ⟨j, ?_⟩
      rw [hj, T_of_odd hodd] at hk
      omega
  · rintro ⟨hn, t, ht⟩
    obtain ⟨k, hk⟩ := exists_T_iterate_eq_F_iterate n t
    exact ⟨hn, k, hk ▸ ht⟩

/-- A set with the transport property, intersected with a merging class, keeps it (the class has
the transport property at every threshold, `transport_class`). -/
lemma transport_inter_class {A : Set ℕ} {q : ℕ → ℝ} {ρ η x₀ : ℝ} (h : Transport A q ρ η x₀)
    (a : ℕ) : Transport (A ∩ mergeClass a) q ρ η x₀ := by
  intro x hx hm1 N hN hc hmT hM
  obtain ⟨h1, h2⟩ := h x hx hm1 N hN hc hmT hM
  obtain ⟨h3, -⟩ := transport_class a x₀ x hx hm1 N hN hc hmT hM
  exact ⟨⟨fun hAB => ⟨h1.mp hAB.1, h3.mp hAB.2⟩, fun hAB => ⟨h1.mpr hAB.1, h3.mpr hAB.2⟩⟩,
    fun hAB => h2 hAB.1⟩

/-- A doubling-compatible set, intersected with a merging class, stays doubling compatible
(`doubling_class`). -/
lemma doubling_inter_class {A : Set ℕ} {q : ℕ → ℝ} {e0 : ℝ} (h : DoublingCompatible A q e0)
    (a : ℕ) : DoublingCompatible (A ∩ mergeClass a) q e0 := by
  obtain ⟨n0, hn0⟩ := h
  obtain ⟨n1, hn1⟩ := doubling_class a
  refine ⟨max n0 n1, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn0 n (le_of_max_le_left hn)
  obtain ⟨h3, -⟩ := hn1 n (le_of_max_le_right hn)
  exact ⟨⟨fun hAB => ⟨h1.mp hAB.1, h3.mp hAB.2⟩, fun hAB => ⟨h1.mpr hAB.1, h3.mpr hAB.2⟩⟩,
    fun hAB => h2 hAB.1⟩

open Classical in
/-- **Corollary 6.11 [`cor:escape`] (deterministic-time escape).** For a divergent class `C` (the
class of a nonrepeating `T`-ray `a`) with density `π_C > 0` and `N_X` uniform on `C ∩ [1, X]`:
(first sentence) with `C_C = C₀/π_C`, for every `K ≥ 1` and all `X ≥ X₀` (`X₀` chosen before `K`,
so the bound holds for every deterministic `t = t(X)` and every `K = K(X)`), `sup_t P(F^t(N_X) ≤ K)
≤ C_C K/√(log X)`; in particular the proportion tends to `0` uniformly in `t` when
`K(X) = o(√(log X))`;
(second sentence) `P(F^t(N_X) ≤ K for some t) → dens(A_K ∩ C)/π_C`, which tends to `1` as
`K → ∞`. -/
theorem escape (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ a : ℕ, 0 < a → NonRepeating a →
      ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
      (∃ X₀ : ℝ, ∀ K : ℕ, 1 ≤ K → ∀ X : ℕ, X₀ ≤ X → ∀ t : ℕ,
        (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K)).card : ℝ) /
          (window (mergeClass a) X).card ≤ C₀ / pC * K / √(Real.log X)) ∧
      (∀ K : ℕ → ℕ, Tendsto (fun X : ℕ => (K X : ℝ) / √(Real.log X)) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, ∀ t : ℕ,
          (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K X)).card : ℝ) /
            (window (mergeClass a) X).card ≤ ε) ∧
      (∀ K : ℕ, 1 ≤ K → ∃ dK : ℝ, HasDensity (AK K ∩ mergeClass a) dK ∧
        Tendsto (fun X : ℕ =>
          (((window (mergeClass a) X).filter (fun n => ∃ t, F^[t] n ≤ K)).card : ℝ) /
            (window (mergeClass a) X).card) atTop (𝓝 (dK / pC))) ∧
      (∀ dK : ℕ → ℝ, (∀ K : ℕ, 1 ≤ K → HasDensity (AK K ∩ mergeClass a) (dK K)) →
        Tendsto (fun K : ℕ => dK K / pC) atTop (𝓝 1)) := by
  obtain ⟨C₁, X₁, hC₁, -, -, hii, -, -⟩ := anticonc hTM hTP
  obtain ⟨dC, hdC, hdCpos, -⟩ := thresholds_iii hTM hTP hθ
  obtain ⟨hexK, Cth, δ0, -, hδ0, hlow⟩ := thresholds_i hTM hTP hθ
  obtain ⟨δb, Cb, xb, -, -, -, hbase⟩ := density_near_base_of_tao hTM hTP hθ 1 1
  refine ⟨2 * C₁, by linarith, fun a ha hR => ?_⟩
  set pC := dC (Quotient.mk mergeSetoid a) with hpCdef
  have hpC : 0 < pC := hdCpos a ha
  have hdens : HasDensity (mergeClass a) pC := by
    rw [mergeClass_eq_classSet]
    exact hdC _
  obtain ⟨N, hN⟩ := exists_half_le_card_window hdens hpC
  -- the first sentence, for every `K ≥ 1` and all `X ≥ X₀`, uniformly in `t`
  have hfirst : ∀ K : ℕ, 1 ≤ K → ∀ X : ℕ, max X₁ N ≤ X → ∀ t : ℕ,
      (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K)).card : ℝ) /
        (window (mergeClass a) X).card ≤ 2 * C₁ / pC * K / √(Real.log X) := by
    intro K _ X hX t
    obtain ⟨hX0, hcnt⟩ := hN X (by exact_mod_cast le_of_max_le_right hX)
    have hlev : ∀ j : ℤ, (levelCount (mergeClass a) (coordF a) j X : ℝ) ≤
        C₁ * X / √(Real.log X) := fun j => (hii X (le_of_max_le_left hX) a ha hR j).1
    -- `F^t(n) = m ≤ K` puts `n` in the level set `{ℓ_C = ℓ_C(m) - t}`
    have hsub : (window (mergeClass a) X).filter (fun n => F^[t] n ≤ K) ⊆
        (Icc 1 K).biUnion (fun m =>
          (window (mergeClass a) X).filter (fun n => coordF a n = coordF a m - t)) := by
      intro n hn
      rw [mem_filter] at hn
      obtain ⟨hnw, hnK⟩ := hn
      have hnC : n ∈ mergeClass a := (mem_window.mp hnw).2
      rw [mem_biUnion]
      refine ⟨F^[t] n, mem_Icc.mpr ⟨iterate_F_pos hnC.1 t, hnK⟩, mem_filter.mpr ⟨hnw, ?_⟩⟩
      rw [coordF_iterate ha hR hnC t]
      ring
    have hnum : (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K)).card : ℝ) ≤
        C₁ * K * X / √(Real.log X) := by
      calc (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K)).card : ℝ)
          ≤ ∑ m ∈ Icc 1 K, (((window (mergeClass a) X).filter
              (fun n => coordF a n = coordF a m - t)).card : ℝ) := by
            exact_mod_cast (card_le_card hsub).trans card_biUnion_le
        _ = ∑ m ∈ Icc 1 K, (levelCount (mergeClass a) (coordF a) (coordF a m - t) X : ℝ) := rfl
        _ ≤ ∑ m ∈ Icc 1 K, C₁ * X / √(Real.log X) := sum_le_sum fun m _ => hlev _
        _ = C₁ * K * X / √(Real.log X) := by
            rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
            ring
    calc _ ≤ 2 * (C₁ * K) / (pC * √(Real.log X)) :=
          div_card_le hpC hX0 hcnt (Nat.cast_nonneg _) hnum
      _ = 2 * C₁ / pC * K / √(Real.log X) := by ring
  refine ⟨pC, hpC, hdens, ⟨max X₁ N, hfirst⟩, fun K hK ε hε => ?_, fun K hK => ?_,
    fun dK hdK => ?_⟩
  · -- `K(X) = o(√(log X))`: apply the first sentence with `K(X) + 1`
    have hs : Tendsto (fun X : ℕ => √(Real.log X)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun X : ℕ => (1 : ℝ) / √(Real.log X)) atTop (𝓝 0) := by
      simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hs
    have hlim : Tendsto (fun X : ℕ => 2 * C₁ / pC * ((K X : ℝ) / √(Real.log X) +
        1 / √(Real.log X))) atTop (𝓝 0) := by
      simpa using (hK.add h1).const_mul (2 * C₁ / pC)
    filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop ⌈max X₁ N⌉₊]
      with X hX hX0 t
    have hX0' : max X₁ N ≤ X := (Nat.le_ceil _).trans (by exact_mod_cast hX0)
    have hb := hfirst (K X + 1) (by omega) X hX0' t
    have hmono : (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K X)).card : ℝ) /
        (window (mergeClass a) X).card ≤
        (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K X + 1)).card : ℝ) /
        (window (mergeClass a) X).card := by
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast card_le_card fun n hn => by
        rw [mem_filter] at hn ⊢
        exact ⟨hn.1, Nat.le_succ_of_le hn.2⟩
    have heq : 2 * C₁ / pC * ((K X + 1 : ℕ) : ℝ) / √(Real.log X) =
        2 * C₁ / pC * ((K X : ℝ) / √(Real.log X) + 1 / √(Real.log X)) := by
      push_cast
      ring
    linarith
  · -- the second sentence: the event is `A_K`, and the ratio of densities
    obtain ⟨dK, hA, -⟩ := hbase (AK K ∩ mergeClass a) (fun n => -(tauK K n : ℝ)) K 1
      (transport_inter_class (transport_AK K) a) (doubling_inter_class (doubling_AK K) a)
    refine ⟨dK, hA, (tendsto_card_div_card hA hdens hpC.ne').congr fun X => ?_⟩
    have hset : window (AK K ∩ mergeClass a) X =
        (window (mergeClass a) X).filter (fun n => ∃ t, F^[t] n ≤ K) := by
      ext n
      simp only [mem_window, mem_filter, Set.mem_inter_iff, AK_eq_F, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hnX, ⟨hn, t, ht⟩, hnC⟩
        exact ⟨⟨hnX, hnC⟩, t, ht⟩
      · rintro ⟨⟨hnX, hnC⟩, t, ht⟩
        exact ⟨hnX, ⟨hnC.1, t, ht⟩, hnC⟩
    rw [hset]
  · -- `dens(A_K ∩ C)/π_C → 1`, from Theorem 1.3(i)
    have h0 : Tendsto (fun K : ℕ => Real.log K ^ (-δ0)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hδ0).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      simpa [Function.comp_def] using this
    have hlo : Tendsto (fun K : ℕ => 1 - Cth / pC * Real.log K ^ (-δ0)) atTop (𝓝 1) := by
      simpa using (h0.const_mul (Cth / pC)).const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with K hK
      obtain ⟨h, hh⟩ := hexK K (by omega)
      have hd := hdK K (by omega)
      have hdiff := HasDensity.diff Set.inter_subset_right hd hdens
      have hsub : mergeClass a \ (AK K ∩ mergeClass a) ⊆ {n | 0 < n ∧ n ∉ AK K} :=
        fun n hn => ⟨hn.1.1, fun hA => hn.2 ⟨hA, hn.1⟩⟩
      have h1 := hdiff.mono hsub hh.compl_pos
      have h2 := hlow K hK h hh
      have e : Cth / pC * Real.log K ^ (-δ0) * pC = Cth * Real.log K ^ (-δ0) := by
        field_simp [hpC.ne']
      rw [le_div_iff₀ hpC, sub_mul, one_mul, e]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with K hK
      rw [div_le_one hpC]
      exact (hdK K hK).mono Set.inter_subset_right hdens

end CollatzCLT
