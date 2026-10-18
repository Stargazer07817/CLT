import LeanClt.Potential.Rays
import LeanClt.Exceptional.Corollaries

/-!
# Proposition 7.5 [`prop:approx`]: approximation by finite orbit potentials

Stage 5 of the checkpoint-17 plan. Fix `K ≥ 2` and `n ≥ 1`, and write `A_k = {N : H_K(N) = k}`.

* **`f_K ≤ h`.** The events `A_k` are disjoint, and `A_k ⊆ P_T(n)` when the odd `k ≤ K` reaches `n`.
  Their densities are `ν_K({k})` (`nuK_base`), so finite additivity gives
  `f_K(n) = ∑_{k reaches n} ν_K({k}) ≤ h(n)`.
* **`h - f_K ≤ C (log K)^{-ε}`.** A source of `P_T(n)` outside these events visits `n` before any
  odd value `≤ K` (otherwise its label reaches `n`), so its label is the label `H_K(n)` of `n` itself
  (`entK_shift`). Thus `P_T(n) ⊆ ⋃_{k reaches n} A_k ∪ {H_K = H_K(n)}`, and the excess is at most one
  atom, which Lemma 7.1 [`lem:diffuse`] bounds.
* **The consequences.** If `h(n) > C (log K)^{-ε}` then `f_K(n) > 0`, so some odd `k ≤ K` reaches `n`.
  For the weighted sum, `∑_{n ∈ F} f_K(n) g(n) = ∑_k ν_K({k}) ∑_{n ∈ F ∩ Orbit(k)} g(n) ≤ B`
  for every finite `F` of positive integers, since `∑_k ν_K({k}) ≤ 1` (`nuK_prob`); letting `K → ∞`
  in `h ≤ f_K + C (log K)^{-ε}` bounds every finite partial sum by `B`.

Natural densities replace v8's odd relative densities; the inclusions hold for every source.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- `H_K(0) = †`: the orbit of `0` is constant and even. -/
lemma entK_zero (K : ℕ) : entK K 0 = none := by
  refine entK_eq_none_iff.mpr fun i => ?_
  rw [Function.iterate_fixed T_zero]
  rintro ⟨h, -⟩
  exact absurd h (by decide)

open Classical in
/-- `f_K(n)` is the sum of the atoms `ν_K({k})` over the odd `k ≤ K` that reach `n`. -/
lemma fK_eq_sum (K n : ℕ) :
    fK K n = ∑ k ∈ ((range (K + 1)).filter Odd).filter (fun k => n ∈ fwdOrbit k), nuK K {some k} := by
  unfold fK
  rw [Finset.sum_filter (fun k => n ∈ fwdOrbit k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- **Proposition 7.5 [`prop:approx`]**, (7.4, `eq:approx`) and the first consequence. -/
theorem approx (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ K : ℕ, 2 ≤ K →
      (∀ n : ℕ, 0 < n → 0 ≤ hpot n - fK K n ∧ hpot n - fK K n ≤ C * (Real.log K) ^ (-ε)) ∧
      (∀ n : ℕ, 0 < n → C * (Real.log K) ^ (-ε) < hpot n →
        ∃ k : ℕ, Odd k ∧ k ≤ K ∧ n ∈ fwdOrbit k) := by
  classical
  obtain ⟨C, ε, hC, hε, hdiff⟩ := diffuse hTM hTP hθ
  obtain ⟨δ', C', x₁, -, -, -, hb⟩ := nuK_base hTM hTP hθ
  have hmain : ∀ K : ℕ, 2 ≤ K → ∀ n : ℕ, 0 < n →
      0 ≤ hpot n - fK K n ∧ hpot n - fK K n ≤ C * (Real.log K) ^ (-ε) := by
    intro K hK n hn
    set S := ((range (K + 1)).filter Odd).filter (fun k => n ∈ fwdOrbit k) with hS
    set A : ℕ → Set ℕ := fun k => {N | entK K N ∈ ({some k} : Set (Option ℕ))} with hA
    have hdisj : (S : Set ℕ).PairwiseDisjoint A := by
      intro k _ k' _ hkk'
      refine Set.disjoint_left.mpr fun N h1 h2 => hkk' ?_
      simp only [hA, Set.mem_ofPred_eq, Set.mem_singleton_iff] at h1 h2
      exact Option.some_injective _ (h1.symm.trans h2)
    have hB : HasDensity (⋃ k ∈ S, A k) (∑ k ∈ S, nuK K {some k}) :=
      hasDensity_biUnion S hdisj fun k _ => (hb K {some k}).1
    have hP := hasDensity_hpot hTM hTP hθ n hn
    rw [fK_eq_sum, ← hS]
    constructor
    · -- `f_K(n) ≤ h(n)`
      have hsub : (⋃ k ∈ S, A k) ⊆ Pred T n := by
        intro N hN
        simp only [Set.mem_iUnion, hA, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hN
        obtain ⟨k, hkS, hNk⟩ := hN
        rw [hS, Finset.mem_filter] at hkS
        obtain ⟨-, j, hj⟩ := hkS
        obtain ⟨i, hi, -, -, -⟩ := entK_eq_some_iff.mp hNk
        have hN0 : 0 < N := by
          rcases Nat.eq_zero_or_pos N with rfl | h
          · rw [entK_zero] at hNk; exact absurd hNk (by simp)
          · exact h
        refine ⟨hN0, j + i, ?_⟩
        rw [Function.iterate_add_apply, hi]
        exact hj
      have := HasDensity.mono hsub hB hP
      linarith
    · -- the excess is at most the atom of the label of `n`
      set e := entK K n with he
      have hsub : Pred T n ⊆ (⋃ k ∈ S, A k) ∪ {N | entK K N ∈ ({e} : Set (Option ℕ))} := by
        rintro N ⟨hN, hreach⟩
        set t := Nat.find hreach with ht
        have htspec : T^[t] N = n := Nat.find_spec hreach
        by_cases hearly : ∃ s < t, Odd (T^[s] N) ∧ T^[s] N ≤ K
        · -- the label of `N` reaches `n`
          left
          obtain ⟨s, hs, hsodd, hsK⟩ := hearly
          have hne : entK K N ≠ none := fun h => entK_eq_none_iff.mp h s ⟨hsodd, hsK⟩
          obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
          obtain ⟨i, hi, hmodd, hmK, hmin⟩ := entK_eq_some_iff.mp hm
          have hit : i ≤ s := by
            by_contra h
            push Not at h
            exact hmin s h ⟨hsodd, hsK⟩
          simp only [Set.mem_iUnion, hA, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          refine ⟨m, ?_, hm⟩
          rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
          refine ⟨⟨by omega, hmodd⟩, t - i, ?_⟩
          change T^[t - i] m = n
          rw [← hi, ← Function.iterate_add_apply, show t - i + i = t by omega, htspec]
        · -- `N` visits `n` before any odd value `≤ K`
          right
          push Not at hearly
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, he]
          exact entK_shift htspec fun s hs ⟨hodd, hle⟩ => absurd hle (not_le.mpr (hearly s hs hodd))
      have hle := HasDensity.le_add_of_subset_union hsub hP hB (hb K {e}).1
      have hatom : nuK K {e} ≤ C * (Real.log K) ^ (-ε) := by
        rcases he' : e with _ | m
        · exact (hdiff K hK).1
        · obtain ⟨hmodd, hmK⟩ := entK_label (he ▸ he')
          exact (hdiff K hK).2 m hmodd hmK
      linarith
  refine ⟨C, ε, hC, hε, fun K hK => ⟨hmain K hK, fun n hn hlt => ?_⟩⟩
  -- the first consequence: `f_K(n) > 0`
  by_contra hno
  push Not at hno
  have hzero : fK K n = 0 := by
    rw [fK_eq_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
    exact absurd hk.2 (hno k hk.1.2 (by omega))
  have := (hmain K hK n hn).2
  rw [hzero, sub_zero] at this
  linarith

/-- **Proposition 7.5 [`prop:approx`], the second consequence.** The orbit-sum hypothesis is
stated over finite subsets of the forward orbit (equivalent for `g ≥ 0`); the sum is over `n ≥ 1`. -/
theorem approx_sum (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (g : ℕ → ℝ) (B : ℝ) (hg : ∀ n, 0 < n → 0 ≤ g n)
    (hB : ∀ k : ℕ, 0 < k → ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ fwdOrbit k → ∑ n ∈ F, g n ≤ B) :
    Summable (fun n : ℕ => hpot (n + 1) * g (n + 1)) ∧
      ∑' n : ℕ, hpot (n + 1) * g (n + 1) ≤ B := by
  classical
  obtain ⟨C, ε, hC, hε, happ⟩ := approx hTM hTP hθ
  have hnn : ∀ n : ℕ, 0 ≤ hpot (n + 1) * g (n + 1) := fun n =>
    mul_nonneg (hpot_nonneg hTM hTP hθ _) (hg _ (by omega))
  -- every finite partial sum is at most `B`
  have hfin : ∀ u : Finset ℕ, ∑ n ∈ u, hpot (n + 1) * g (n + 1) ≤ B := by
    intro u
    set F := u.image (· + 1) with hF
    have hFpos : ∀ m ∈ F, 0 < m := by
      intro m hm
      rw [hF, Finset.mem_image] at hm
      obtain ⟨n, -, rfl⟩ := hm
      omega
    have hsum : ∑ n ∈ u, hpot (n + 1) * g (n + 1) = ∑ m ∈ F, hpot m * g m := by
      rw [hF, Finset.sum_image fun a _ b _ h => by omega]
    rw [hsum]
    set G := ∑ m ∈ F, g m with hG
    -- the bound at each `K`
    have hK : ∀ K : ℕ, 2 ≤ K → ∑ m ∈ F, hpot m * g m ≤ B + C * Real.log K ^ (-ε) * G := by
      intro K hK
      have h1 : ∀ m ∈ F, hpot m * g m ≤ fK K m * g m + C * Real.log K ^ (-ε) * g m := by
        intro m hm
        have := ((happ K hK).1 m (hFpos m hm)).2
        have hgm := hg m (hFpos m hm)
        nlinarith
      have h2 : ∑ m ∈ F, fK K m * g m ≤ B := by
        set Fo := (range (K + 1)).filter Odd with hFo
        have e1 : ∑ m ∈ F, fK K m * g m =
            ∑ k ∈ Fo, nuK K {some k} * ∑ m ∈ F.filter (fun m => m ∈ fwdOrbit k), g m := by
          simp only [fK, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Set.indicator_apply]
          split_ifs <;> ring
        rw [e1]
        obtain ⟨hν0, hν1, -⟩ := nuK_prob hTM hTP hθ K
        have hB0 : 0 ≤ B := by simpa using hB 1 one_pos ∅ (by simp)
        have h3 : ∀ k ∈ Fo, nuK K {some k} * ∑ m ∈ F.filter (fun m => m ∈ fwdOrbit k), g m ≤
            nuK K {some k} * B := by
          intro k hk
          rw [hFo, Finset.mem_filter] at hk
          refine mul_le_mul_of_nonneg_left (hB k hk.2.pos _ fun m hm => ?_) (hν0 _)
          rw [Finset.mem_coe, Finset.mem_filter] at hm
          exact hm.2
        have h4 : ∑ k ∈ Fo, nuK K {some k} ≤ 1 := by linarith [hν0 none]
        calc _ ≤ ∑ k ∈ Fo, nuK K {some k} * B := Finset.sum_le_sum h3
          _ = (∑ k ∈ Fo, nuK K {some k}) * B := by rw [Finset.sum_mul]
          _ ≤ 1 * B := mul_le_mul_of_nonneg_right h4 hB0
          _ = B := one_mul B
      calc ∑ m ∈ F, hpot m * g m
          ≤ ∑ m ∈ F, (fK K m * g m + C * Real.log K ^ (-ε) * g m) := Finset.sum_le_sum h1
        _ = ∑ m ∈ F, fK K m * g m + C * Real.log K ^ (-ε) * G := by
            rw [Finset.sum_add_distrib, hG, Finset.mul_sum]
        _ ≤ B + C * Real.log K ^ (-ε) * G := by linarith
    -- letting `K → ∞`
    have hlim : Tendsto (fun K : ℕ => B + C * Real.log K ^ (-ε) * G) atTop (𝓝 B) := by
      have h0 := ((tendsto_rpow_neg_atTop hε).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
      have := tendsto_const_nhds (x := B).add (h0.mul_const G)
      simpa [Function.comp_def] using this
    exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨2, hK⟩)
  have hsumm : Summable (fun n : ℕ => hpot (n + 1) * g (n + 1)) := summable_of_sum_le hnn hfin
  exact ⟨hsumm, tsum_le_of_sum_le (fun n => hnn n) hfin⟩

end CollatzCLT
