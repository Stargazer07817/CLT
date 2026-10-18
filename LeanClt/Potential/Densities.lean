import LeanClt.Potential.Defs
import LeanClt.Transfer.AdjacentUniform
import LeanClt.Exceptional.Laws

/-!
# §7: the densities `h(n)`, the flow identity (7.2), and the entrance law `ν_K`

Stage 2 of the checkpoint-17 plan. Every statement about `h` and `ν_K` here takes the standing
hypotheses `TaoMajorant`, `TaoPrefix` and `IrrMeasure d ϰ`, through `density_near_base_of_tao`: the
chain estimate (6.7, `eq:chain`) at `s = 0`, with constants uniform in the set, the clock and the
threshold. The finite-sample facts (`hasDensity_singleton`, `lawHK_eq_sum`, `lawHK_nonneg`,
`lawHK_le_one`, `lawHK_univ`, `indicator_entK_decomp`, `lawHK_decomp`) are unconditional.

* `hasDensity_hpot`: `P_T(n)` is the basin of `{n}`, which has the transport property and is doubling
  compatible (`transport_reach`, `doubling_reach`), so its density exists. No positivity is used.
* `flow_density`, the density identity (7.2, `eq:flow`) of Proposition 7.3 [`prop:flow`]: the set-level
  decomposition `pred_flow_eq`, `pred_flow_disjoint` and finite additivity.
* `nuK_base`: for every `K` and every set of labels `E`, `{H_K ∈ E}` has density `ν_K(E)`, and
  `|ν_K(E) - P(H_K(N_B) ∈ E)| ≤ C (log B)^{-δ}` for every base `B ≥ max(x₁, K)^α`, with `δ, C, x₁`
  independent of `K` and `E` (`transport_entK`, `doubling_entK`).
* `nuK_tendsto`, `nuK_prob` (`ν_K` is a probability law on `{k odd, k ≤ K} ∪ {†}`; finite additivity
  `lawHK_decomp` of the sample law), `nuK_none` (`ν_K(†) = 1 - h_K`) and `nuK_l1`, the `ℓ¹` bound
  (7.1, `eq:nuK`). `nuK_l1` is uniform in `K` because the `ℓ¹` distance of two probability vectors is
  twice the excess on the set `E₊` where the sample law is larger, and `nuK_base` bounds that one set.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## Finite-sample facts -/

/-- A single point has density `0`. -/
lemma hasDensity_singleton (n : ℕ) : HasDensity {n} 0 := by
  refine hasDensity_zero_of_le (g := fun _ => 1) ?_ (Eventually.of_forall fun X => ?_)
  · simpa using (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0))
  · have : (window {n} X).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      rw [mem_window] at ha hb
      exact ha.2.trans hb.2.symm
    exact_mod_cast this

open Classical in
lemma lawHK_eq_sum (K : ℕ) (Y : ℝ) (E : Set (Option ℕ)) :
    lawHK K Y E =
      (∑ N ∈ oddClosed Y, if entK K N ∈ E then (1 : ℝ) else 0) / (oddClosed Y).card := by
  unfold lawHK
  rw [Finset.card_filter]
  push_cast
  rfl

lemma lawHK_nonneg (K : ℕ) (Y : ℝ) (E : Set (Option ℕ)) : 0 ≤ lawHK K Y E := by
  unfold lawHK; positivity

lemma lawHK_le_one (K : ℕ) (Y : ℝ) (E : Set (Option ℕ)) : lawHK K Y E ≤ 1 := by
  classical
  unfold lawHK
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le _ _) (Nat.cast_nonneg _)

lemma lawHK_univ {K : ℕ} {Y : ℝ} (hY : 4 ≤ Y) : lawHK K Y Set.univ = 1 := by
  classical
  have hpos : (0 : ℝ) < (oddClosed Y).card := LY_pos hY
  unfold lawHK
  convert div_self hpos.ne' using 4
  ext N
  simp

open Classical in
/-- Pointwise decomposition of `1{H_K(N) ∈ E}` over the labels. -/
lemma indicator_entK_decomp (K N : ℕ) (E : Set (Option ℕ)) :
    (if entK K N ∈ E then (1 : ℝ) else 0) =
      (if none ∈ E then (if entK K N = none then (1 : ℝ) else 0) else 0) +
      ∑ k ∈ (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ E),
        (if entK K N = some k then (1 : ℝ) else 0) := by
  rcases h : entK K N with _ | m
  · simp
  · obtain ⟨hodd, hle⟩ := entK_label h
    have hmem : m ∈ (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ E) ↔ some m ∈ E := by
      simp [Finset.mem_filter, hodd, Nat.lt_succ_of_le hle]
    simp only [reduceCtorEq, ite_false, Option.some.injEq]
    rw [Finset.sum_ite_eq]
    by_cases hE : some m ∈ E
    · simp [hE, hmem.mpr hE]
    · simp [hE, mt hmem.mp hE]

open Classical in
/-- **Finite additivity of the sample law** over the labels `{k odd, k ≤ K} ∪ {†}`. -/
lemma lawHK_decomp (K : ℕ) (Y : ℝ) (E : Set (Option ℕ)) :
    lawHK K Y E = (if none ∈ E then lawHK K Y {none} else 0) +
      ∑ k ∈ (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ E), lawHK K Y {some k} := by
  simp only [lawHK_eq_sum, Set.mem_singleton_iff]
  rw [← Finset.sum_div, Finset.sum_congr rfl (fun N _ => indicator_entK_decomp K N E),
    Finset.sum_add_distrib, Finset.sum_comm (s := oddClosed Y), add_div]
  congr 1
  by_cases hE : none ∈ E
  · simp only [hE, ite_true]
  · simp only [hE, ite_false, Finset.sum_const_zero, zero_div]

/-! ## The densities `h(n)` and the flow identity -/

/-- §7, opening paragraph: `h(n) = dens P_T(n)` exists for every `n ≥ 1`. -/
theorem hasDensity_hpot (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (n : ℕ) (hn : 0 < n) : HasDensity (Pred T n) (hpot n) := by
  obtain ⟨δ, C, x₁, -, -, -, hdens⟩ := density_near_base_of_tao hTM hTP hθ 1 1
  have htr : Transport (Pred T n) (fun m => -(entry {n} m : ℝ)) 1 1 n := by
    rw [pred_eq_reach]
    exact transport_reach (fun m hm => by rw [Set.mem_singleton_iff.mp hm])
  have hdb : DoublingCompatible (Pred T n) (fun m => -(entry {n} m : ℝ)) 1 := by
    rw [pred_eq_reach]
    exact doubling_reach (n0 := n + 1) (by omega) (fun m hm h => by
      rw [Set.mem_singleton_iff] at h; omega)
  obtain ⟨p, hp, -⟩ := hdens (Pred T n) _ n 1 htr hdb
  rw [hpot, natDens_eq hp]
  exact hp

/-- **Proposition 7.3 [`prop:flow`]**, the density identity (7.2, `eq:flow`). -/
theorem flow_density (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {n : ℕ} (hn : 0 < n) (hper : ¬ IsPeriodic n) :
    hpot n = hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0) := by
  have h1 := hasDensity_hpot hTM hTP hθ n hn
  have h2 := hasDensity_hpot hTM hTP hθ (2 * n) (by omega)
  obtain ⟨hd1, hd2, hd3⟩ := pred_flow_disjoint hn hper
  have hob : HasDensity (oddBranch n) (if n % 6 = 4 then hpot ((n - 1) / 3) else 0) := by
    unfold oddBranch
    split_ifs with h6
    · exact hasDensity_hpot hTM hTP hθ _ (by omega)
    · exact hasDensity_empty
  have hu := ((hasDensity_singleton n).union (Set.disjoint_singleton_left.mpr hd1) h2).union
    (Set.disjoint_union_left.mpr ⟨Set.disjoint_singleton_left.mpr hd2, hd3⟩) hob
  rw [← pred_flow_eq hn] at hu
  have := h1.unique hu
  linarith

/-! ## The entrance law `ν_K` -/

/-- **The chain estimate at a base, for the events `{H_K ∈ E}`.** `δ, C, x₁` do not depend on `K`
or `E`. -/
theorem nuK_base (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ δ C x₁ : ℝ, 0 < δ ∧ 0 ≤ C ∧ 1 < x₁ ∧ ∀ (K : ℕ) (E : Set (Option ℕ)),
      HasDensity {N | entK K N ∈ E} (nuK K E) ∧
      ∀ B : ℝ, (max x₁ K) ^ alpha ≤ B → |nuK K E - lawHK K B E| ≤ C * (Real.log B) ^ (-δ) := by
  obtain ⟨δ, C, x₁, hδ, hC, hx₁, hdens⟩ := density_near_base_of_tao hTM hTP hθ 0 0
  refine ⟨δ, C, x₁, hδ, hC, hx₁, fun K E => ?_⟩
  obtain ⟨p, hp, hbase⟩ :=
    hdens {N | entK K N ∈ E} (fun _ => 0) K 0 (transport_entK K E) (doubling_entK K E)
  have hlaw : ∀ B, (oddCF {N | entK K N ∈ E} (fun _ => 0) 0 B 0).re = lawHK K B E := fun B => by
    rw [oddCF_zero_re]; rfl
  have hg : Tendsto (fun B : ℝ => C * Real.log B ^ (-δ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop).const_mul C
    simpa using this
  have htend : Tendsto (fun Y : ℝ => lawHK K Y E) atTop (𝓝 p) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub hg) (by simpa using tendsto_const_nhds.add hg) ?_ ?_
    · filter_upwards [eventually_ge_atTop ((max x₁ K) ^ alpha)] with B hB
      have := abs_le.mp (hbase B hB); rw [hlaw] at this; linarith
    · filter_upwards [eventually_ge_atTop ((max x₁ K) ^ alpha)] with B hB
      have := abs_le.mp (hbase B hB); rw [hlaw] at this; linarith
  have hnu : nuK K E = p := nuK_eq htend
  refine ⟨hnu ▸ hp, fun B hB => ?_⟩
  rw [hnu, ← hlaw]
  exact hbase B hB

/-- §7.2: the limits `ν_K(E)` exist, for every `K` (v8 defines `H_K` for `K ≥ 2`). -/
theorem nuK_tendsto (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (K : ℕ) (E : Set (Option ℕ)) :
    Tendsto (fun Y : ℝ => lawHK K Y E) atTop (𝓝 (nuK K E)) := by
  obtain ⟨δ, C, x₁, hδ, -, -, hb⟩ := nuK_base hTM hTP hθ
  have hg : Tendsto (fun B : ℝ => C * Real.log B ^ (-δ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop).const_mul C
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hg) (by simpa using tendsto_const_nhds.add hg) ?_ ?_
  · filter_upwards [eventually_ge_atTop ((max x₁ K) ^ alpha)] with B hB
    have := abs_le.mp ((hb K E).2 B hB); linarith
  · filter_upwards [eventually_ge_atTop ((max x₁ K) ^ alpha)] with B hB
    have := abs_le.mp ((hb K E).2 B hB); linarith

open Classical in
/-- §7.2: `ν_K` is a probability law on `{k odd, k ≤ K} ∪ {†}`. -/
theorem nuK_prob (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (K : ℕ) :
    (∀ e : Option ℕ, 0 ≤ nuK K {e}) ∧
    nuK K {none} + ∑ k ∈ (range (K + 1)).filter Odd, nuK K {some k} = 1 ∧
    ∀ E : Set (Option ℕ), nuK K E = (if none ∈ E then nuK K {none} else 0) +
      ∑ k ∈ (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ E), nuK K {some k} := by
  have hT := nuK_tendsto hTM hTP hθ K
  -- additivity, by passing to the limit in `lawHK_decomp`
  have hadd : ∀ E : Set (Option ℕ), nuK K E = (if none ∈ E then nuK K {none} else 0) +
      ∑ k ∈ (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ E), nuK K {some k} := by
    intro E
    refine tendsto_nhds_unique (hT E) ?_
    simp_rw [lawHK_decomp K _ E]
    refine Tendsto.add ?_ (tendsto_finsetSum _ fun k _ => hT {some k})
    by_cases hE : none ∈ E
    · simpa [hE] using hT {none}
    · simp [hE]
  refine ⟨fun e => ge_of_tendsto' (hT {e}) fun Y => lawHK_nonneg K Y {e}, ?_, hadd⟩
  have h1 : nuK K Set.univ = 1 := by
    refine nuK_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with Y hY
    exact (lawHK_univ hY).symm
  have := hadd Set.univ
  simp only [Set.mem_univ, ite_true, and_true] at this
  linarith

/-- §7.2: the cemetery mass is `ν_K(†) = 1 - h_K`, `h_K = dens A_K`. -/
theorem nuK_none (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (K : ℕ) (hK : 1 ≤ K) : HasDensity (AK K) (1 - nuK K {none}) := by
  clear hK
  obtain ⟨δ, C, x₁, -, -, -, hb⟩ := nuK_base hTM hTP hθ
  refine ((hb K {none}).1.compl_pos).congr_pos fun N hN => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hN, true_and]
  exact entK_ne_none_iff K hN

/-- §7.2, (7.1, `eq:nuK`): the `ℓ¹` distance between the law of `H_K(N_Y)` and `ν_K`, over the
labels `{k odd, k ≤ K} ∪ {†}` (the full `ℓ¹` norm, no factor `1/2`, as in §2.1), for `Y ≥ K^α`,
uniformly in `K ≥ 2`. -/
theorem nuK_l1 (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C δ0 : ℝ, 0 < C ∧ 0 < δ0 ∧ ∀ K : ℕ, 2 ≤ K → ∀ Y : ℝ, (K : ℝ) ^ alpha ≤ Y →
      |lawHK K Y {none} - nuK K {none}| +
        ∑ k ∈ (range (K + 1)).filter Odd, |lawHK K Y {some k} - nuK K {some k}| ≤
        2 * C * (Real.log Y) ^ (-δ0) := by
  classical
  obtain ⟨δ, C, x₁, hδ, hC, hx₁, hb⟩ := nuK_base hTM hTP hθ
  set x₂ := max x₁ 4 with hx₂
  have hx₂4 : (4 : ℝ) ≤ x₂ := le_max_right _ _
  have hα : (1 : ℝ) < alpha := by unfold alpha; norm_num
  have hLx₂ : 0 < alpha * Real.log x₂ := mul_pos (by linarith) (Real.log_pos (by linarith))
  set C' := max C ((alpha * Real.log x₂) ^ δ) with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le (Real.rpow_pos_of_pos hLx₂ δ) (le_max_right _ _)
  refine ⟨C', δ, hC'pos, hδ, fun K hK Y hY => ?_⟩
  obtain ⟨hnn, hsum1, hadd⟩ := nuK_prob hTM hTP hθ K
  set F := (range (K + 1)).filter Odd with hF
  -- the sample law has total mass at most `1`
  have hsumA : lawHK K Y {none} + ∑ k ∈ F, lawHK K Y {some k} ≤ 1 := by
    have := lawHK_decomp K Y Set.univ
    simp only [Set.mem_univ, ite_true, and_true] at this
    rw [← this]; exact lawHK_le_one K Y _
  have hK1 : (1 : ℝ) < K := by exact_mod_cast hK
  have hY1 : 1 < Y := lt_of_lt_of_le (Real.one_lt_rpow hK1 (by linarith)) hY
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  by_cases hbig : (max x₂ K) ^ alpha ≤ Y
  · -- the main case: twice the excess on `E₊ = {e : law > ν}`
    have hY4 : 4 ≤ Y := by
      have h1 : (4 : ℝ) ≤ max x₂ K := hx₂4.trans (le_max_left _ _)
      have h2 : max x₂ K ≤ (max x₂ K) ^ alpha :=
        Real.self_le_rpow_of_one_le (by linarith) hα.le
      linarith
    have hsumA1 : lawHK K Y {none} + ∑ k ∈ F, lawHK K Y {some k} = 1 := by
      have := lawHK_decomp K Y Set.univ
      simp only [Set.mem_univ, ite_true, and_true] at this
      rw [← this]; exact lawHK_univ hY4
    set Ep : Set (Option ℕ) := {e | nuK K {e} < lawHK K Y {e}} with hEp
    have hbase : (max x₁ K) ^ alpha ≤ Y :=
      le_trans (Real.rpow_le_rpow (by positivity) (max_le_max (le_max_left _ _) le_rfl)
        (by linarith)) hbig
    have hEbound := (hb K Ep).2 Y hbase
    -- `|x| = 2 max(x, 0) - x`, summed over the labels
    have hpos_part : lawHK K Y Ep - nuK K Ep =
        max (lawHK K Y {none} - nuK K {none}) 0 +
          ∑ k ∈ F, max (lawHK K Y {some k} - nuK K {some k}) 0 := by
      have hfilt : (range (K + 1)).filter (fun k => Odd k ∧ some k ∈ Ep) =
          F.filter (fun k => some k ∈ Ep) := by
        rw [hF, Finset.filter_filter]
      have e1 : lawHK K Y Ep = (if none ∈ Ep then lawHK K Y {none} else 0) +
          ∑ k ∈ F, (if some k ∈ Ep then lawHK K Y {some k} else 0) := by
        rw [lawHK_decomp K Y Ep, hfilt, Finset.sum_filter]
      have e2 : nuK K Ep = (if none ∈ Ep then nuK K {none} else 0) +
          ∑ k ∈ F, (if some k ∈ Ep then nuK K {some k} else 0) := by
        rw [hadd Ep, hfilt, Finset.sum_filter]
      rw [e1, e2]
      have hnone : (if none ∈ Ep then lawHK K Y {none} else 0) -
          (if none ∈ Ep then nuK K {none} else 0) = max (lawHK K Y {none} - nuK K {none}) 0 := by
        by_cases h : none ∈ Ep
        · simp only [h, ite_true]; simp only [hEp, Set.mem_ofPred_eq] at h
          rw [max_eq_left (by linarith)]
        · simp only [h, ite_false, sub_zero]; simp only [hEp, Set.mem_ofPred_eq, not_lt] at h
          rw [max_eq_right (by linarith)]
      have hsome : ∀ k ∈ F, (if some k ∈ Ep then lawHK K Y {some k} else 0) -
          (if some k ∈ Ep then nuK K {some k} else 0) =
          max (lawHK K Y {some k} - nuK K {some k}) 0 := by
        intro k _
        by_cases h : some k ∈ Ep
        · simp only [h, ite_true]; simp only [hEp, Set.mem_ofPred_eq] at h
          rw [max_eq_left (by linarith)]
        · simp only [h, ite_false, sub_zero]; simp only [hEp, Set.mem_ofPred_eq, not_lt] at h
          rw [max_eq_right (by linarith)]
      rw [← Finset.sum_congr rfl hsome, Finset.sum_sub_distrib, ← hnone]
      ring
    have habs : ∀ x : ℝ, |x| = 2 * max x 0 - x := fun x => by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    have hlhs : |lawHK K Y {none} - nuK K {none}| +
        ∑ k ∈ F, |lawHK K Y {some k} - nuK K {some k}| = 2 * (lawHK K Y Ep - nuK K Ep) := by
      rw [hpos_part]
      simp only [habs, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linarith
    rw [hlhs]
    have h1 : lawHK K Y Ep - nuK K Ep ≤ C * Real.log Y ^ (-δ) := by
      have := (abs_le.mp hEbound).1; linarith
    have h2 : C * Real.log Y ^ (-δ) ≤ C' * Real.log Y ^ (-δ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlogY.le _)
    linarith
  · -- the bounded range: the left side is at most `2`
    push Not at hbig
    have hKx : (K : ℝ) < x₂ := by
      by_contra h
      push Not at h
      rw [max_eq_right h] at hbig
      linarith
    have hYx : Y ≤ x₂ ^ alpha := by
      rw [max_eq_left hKx.le] at hbig; exact hbig.le
    have hlog_le : Real.log Y ≤ alpha * Real.log x₂ := by
      have := Real.log_le_log (by linarith) hYx
      rwa [Real.log_rpow (by linarith)] at this
    have hpow : (alpha * Real.log x₂) ^ (-δ) ≤ Real.log Y ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hlogY hlog_le (by linarith)
    have hone : 1 ≤ C' * Real.log Y ^ (-δ) := by
      have e : (alpha * Real.log x₂) ^ δ * (alpha * Real.log x₂) ^ (-δ) = 1 := by
        rw [← Real.rpow_add hLx₂]; simp
      calc (1 : ℝ) = (alpha * Real.log x₂) ^ δ * (alpha * Real.log x₂) ^ (-δ) := e.symm
        _ ≤ C' * Real.log Y ^ (-δ) :=
          mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg hLx₂.le _) hC'pos.le
    have htri : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |a - b| ≤ a + b := fun a b ha hb => by
      rw [abs_le]; constructor <;> linarith
    have hle : |lawHK K Y {none} - nuK K {none}| +
        ∑ k ∈ F, |lawHK K Y {some k} - nuK K {some k}| ≤
        (lawHK K Y {none} + ∑ k ∈ F, lawHK K Y {some k}) +
          (nuK K {none} + ∑ k ∈ F, nuK K {some k}) := by
      have hs : ∑ k ∈ F, |lawHK K Y {some k} - nuK K {some k}| ≤
          ∑ k ∈ F, (lawHK K Y {some k} + nuK K {some k}) :=
        Finset.sum_le_sum fun k _ => htri _ _ (lawHK_nonneg _ _ _) (hnn _)
      rw [Finset.sum_add_distrib] at hs
      have := htri _ _ (lawHK_nonneg K Y {none}) (hnn none)
      linarith
    linarith

end CollatzCLT
