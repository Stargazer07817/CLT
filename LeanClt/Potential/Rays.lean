import LeanClt.Potential.Diffuse

/-!
# Proposition 7.2 [`prop:raydecay`] and Corollary 7.4 [`cor:conservation`]

Stage 4 of the checkpoint-17 plan.

* **Backward rays** (unconditional). Along a ray `T(v_{j+1}) = v_j`, `T^i(v_{i+j}) = v_j`
  (`ray_iter`). Each `k` reaches only finitely many `v_j` (`reach_ray_finite`): a reached `v_j` is
  either an early state of the orbit of `k`, before its first visit to `v_0`, or a later state, hence a
  point of the forward orbit of `v_0`; in the second case `v_0` is periodic unless `j = 0`, and then
  its forward orbit is finite. Since `v` is injective, finitely many `j` remain.
* **Proposition 7.2.** Fix `K ≥ max(2, v_0)`. For large `j` no `k ≤ K` reaches `v_j`, and `v_i > K`
  for all `i ≥ j₁`. Then every source in `P_T(v_j)` meets no odd value `≤ K` before `v_j`, and the orbit
  from `v_j` meets none before `v_{j₁}`, so `H_K(N) = H_K(v_{j₁}) =: b_K` on all of `P_T(v_j)`, odd or
  even (`entK_shift`); `b_K ≠ †` because `v_{j₁}` reaches `v_0 ≤ K`. Hence
  `h(v_j) ≤ ν_K({b_K}) ≤ C (log K)^{-ε}` by Lemma 7.1 [`lem:diffuse`], with natural densities
  (v8 takes odd relative densities; the inclusion holds for every source, so this is not needed).
* **Corollary 7.4.** The second clause is Proposition 7.2 on the dyadic ray `2^A n`. For the identity
  (7.3, `eq:conservation`): every `2^a n` is nonperiodic when `n` is (it reaches `n`), and
  `2^a n ≡ 4 (6)` iff `a ≥ 1` and `2^a n ≡ 1 (3)` for odd `n`, so (7.2) at `2^a n` reads
  `h(2^a n) = h(2^{a+1} n) + f(a)`; telescoping gives `h(n) = h(2^A n) + ∑_{a<A} f(a)`, and the
  partial sums of the nonnegative series converge to `h(n)`.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## Backward rays (unconditional) -/

/-- Along a backward ray, `T^i(v_{i+j}) = v_j`. -/
lemma ray_iter {v : ℕ → ℕ} (hstep : ∀ j, T (v (j + 1)) = v j) :
    ∀ i j, T^[i] (v (i + j)) = v j := by
  intro i
  induction i with
  | zero => intro j; simp
  | succ i ih =>
    intro j
    rw [Function.iterate_succ_apply, show i + 1 + j = (i + j) + 1 by omega, hstep, ih]

/-- Every `k` reaches only finitely many points of a backward ray of distinct integers. -/
lemma reach_ray_finite {v : ℕ → ℕ} (hinj : Function.Injective v)
    (hstep : ∀ j, T (v (j + 1)) = v j) (k : ℕ) : {j | ∃ t, T^[t] k = v j}.Finite := by
  classical
  have hback : ∀ j, T^[j] (v j) = v 0 := fun j => by simpa using ray_iter hstep j 0
  by_cases h0 : ∃ t, T^[t] k = v 0
  · set τ := Nat.find h0 with hτ
    have hτspec : T^[τ] k = v 0 := Nat.find_spec h0
    -- a reached `v j` is an early state of `k` or on the forward orbit of `v 0`
    have hsub : ∀ j t, T^[t] k = v j → t < τ ∨ ∃ s, T^[s] (v 0) = v j := by
      intro j t ht
      by_cases htτ : t < τ
      · exact Or.inl htτ
      · refine Or.inr ⟨t - τ, ?_⟩
        rw [← hτspec, ← Function.iterate_add_apply, show t - τ + τ = t by omega, ht]
    set early := (range τ).image (fun t => T^[t] k) with hearly
    by_cases hper : IsPeriodic (v 0)
    · obtain ⟨p, hp, hpv⟩ := hper
      have hfin : ∀ s, T^[s] (v 0) = T^[s % p] (v 0) := fun s => by
        conv_lhs => rw [← Nat.mod_add_div s p]
        rw [Function.iterate_add_apply, iterate_period_mul hpv]
      refine (Set.Finite.preimage hinj.injOn
        (early ∪ (range p).image (fun i => T^[i] (v 0))).finite_toSet).subset ?_
      rintro j ⟨t, ht⟩
      simp only [Set.mem_preimage, Finset.coe_union, Set.mem_union, Finset.mem_coe,
        Finset.mem_image, Finset.mem_range, hearly]
      rcases hsub j t ht with h | ⟨s, hs⟩
      · exact Or.inl ⟨t, h, ht⟩
      · exact Or.inr ⟨s % p, Nat.mod_lt _ hp, by rw [← hfin, hs]⟩
    · refine (Set.Finite.preimage hinj.injOn (insert (v 0) early).finite_toSet).subset ?_
      rintro j ⟨t, ht⟩
      simp only [Set.mem_preimage, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
        Finset.mem_image, Finset.mem_range, hearly]
      rcases hsub j t ht with h | ⟨s, hs⟩
      · exact Or.inr ⟨t, h, ht⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · exact Or.inl rfl
        · exfalso
          apply hper
          refine ⟨j + s, by omega, ?_⟩
          rw [Function.iterate_add_apply, hs, hback]
  · convert Set.finite_empty
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro t ht
    exact h0 ⟨j + t, by rw [Function.iterate_add_apply, ht, hback]⟩

/-! ## Proposition 7.2 -/

/-- **Proposition 7.2 [`prop:raydecay`].** -/
theorem raydecay (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (v : ℕ → ℕ) (hv : ∀ j, 0 < v j) (hinj : Function.Injective v)
    (hstep : ∀ j, T (v (j + 1)) = v j) :
    Tendsto (fun j => hpot (v j)) atTop (𝓝 0) := by
  classical
  obtain ⟨C, ε, hC, hε, hdiff⟩ := diffuse hTM hTP hθ
  obtain ⟨δ', C', x₁, -, -, -, hb⟩ := nuK_base hTM hTP hθ
  have hnn : ∀ j, 0 ≤ hpot (v j) := fun j => (hasDensity_hpot hTM hTP hθ _ (hv j)).nonneg
  have hback : ∀ j, T^[j] (v j) = v 0 := fun j => by simpa using ray_iter hstep j 0
  -- the bound at a fixed `K ≥ max(2, v_0)`
  have hK : ∀ K : ℕ, 2 ≤ K → v 0 ≤ K →
      ∀ᶠ j in atTop, hpot (v j) ≤ C * Real.log K ^ (-ε) := by
    intro K hK2 hK0
    -- `j₀`: no `k ≤ K` reaches `v_j` for `j > j₀`
    have hJ : (⋃ k ∈ range (K + 1), {j | ∃ t, T^[t] k = v j}).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => reach_ray_finite hinj hstep k
    obtain ⟨j0, hj0⟩ := hJ.bddAbove
    -- `j₁`: `v_i > K` for `i > j₁`
    have hI : (v ⁻¹' Set.Iic K).Finite := (Set.finite_Iic K).preimage hinj.injOn
    obtain ⟨j1, hj1⟩ := hI.bddAbove
    have hbig : ∀ i, j1 < i → K < v i := fun i hi => by
      by_contra h
      push Not at h
      exact absurd (hj1 (show i ∈ v ⁻¹' Set.Iic K from h)) (by omega)
    -- the label `b_K`
    set jb := j1 + 1 with hjb
    set e := entK K (v jb) with he
    have hene : e ≠ none := (entK_ne_none_iff K (hv jb)).mpr ⟨hv jb, jb, by rw [hback]; exact hK0⟩
    obtain ⟨b, hbe⟩ := Option.ne_none_iff_exists'.mp hene
    obtain ⟨hbodd, hbK⟩ := entK_label (he ▸ hbe)
    filter_upwards [eventually_gt_atTop (max j0 jb)] with j hj
    have hj0' : j0 < j := lt_of_le_of_lt (le_max_left _ _) hj
    have hjb' : jb < j := lt_of_le_of_lt (le_max_right _ _) hj
    -- `H_K(v_j) = H_K(v_{jb})`
    have hvj : entK K (v j) = e := by
      have hk : T^[j - jb] (v j) = v jb := by
        have := ray_iter hstep (j - jb) jb
        rwa [show j - jb + jb = j by omega] at this
      refine entK_shift hk fun s hs => ?_
      have hs' : T^[s] (v j) = v (j - s) := by
        have := ray_iter hstep s (j - s)
        rwa [show s + (j - s) = j by omega] at this
      rw [hs']
      rintro ⟨-, hle⟩
      have := hbig (j - s) (by omega)
      omega
    -- every source of `P_T(v_j)` has the label `b_K`
    have hsub : Pred T (v j) ⊆ {N | entK K N ∈ ({some b} : Set (Option ℕ))} := by
      rintro N ⟨hN, hreach⟩
      rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, ← hbe, ← hvj]
      set t := Nat.find hreach with ht
      have htspec : T^[t] N = v j := Nat.find_spec hreach
      refine entK_shift htspec fun s hs => ?_
      rintro ⟨-, hle⟩
      -- `T^s(N) ≤ K` reaches `v_j`, so `j ≤ j₀`
      have hmem : j ∈ ⋃ k ∈ range (K + 1), {j | ∃ t, T^[t] k = v j} := by
        refine Set.mem_biUnion (x := T^[s] N) (by rw [Finset.mem_coe, Finset.mem_range]; omega) ?_
        refine ⟨t - s, ?_⟩
        rw [← Function.iterate_add_apply, show t - s + s = t by omega, htspec]
      exact absurd (hj0 hmem) (by omega)
    have hle := HasDensity.mono hsub (hasDensity_hpot hTM hTP hθ _ (hv j)) (hb K {some b}).1
    exact hle.trans ((hdiff K hK2).2 b hbodd hbK)
  -- letting `K → ∞`
  have hlim : Tendsto (fun K : ℕ => C * Real.log K ^ (-ε)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hε).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
    simpa [Function.comp_def] using this
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (hnn j), fun a ha => ?_⟩
  obtain ⟨K, hKa, hK2, hK0⟩ := ((hlim.eventually (gt_mem_nhds ha)).and
    ((eventually_ge_atTop 2).and (eventually_ge_atTop (v 0)))).exists
  filter_upwards [hK K hK2 hK0] with j hj
  exact lt_of_le_of_lt hj hKa

/-! ## Corollary 7.4 -/

/-- `h ≥ 0` everywhere (`P_T(0) = ∅`). -/
lemma hpot_nonneg (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (n : ℕ) : 0 ≤ hpot n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Pred T 0 = ∅ := by
      ext m
      simp only [Pred, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        not_exists]
      intro hm k hk
      exact (iterate_T_pos hm k).ne' hk
    rw [hpot, this, natDens_eq hasDensity_empty]
  · exact (hasDensity_hpot hTM hTP hθ n hn).nonneg

/-- Halving: `T^a(2^a n) = n`. -/
lemma iterate_two_pow_mul (a n : ℕ) : T^[a] (2 ^ a * n) = n := by
  induction a with
  | zero => simp
  | succ a ih => rw [Function.iterate_succ_apply, show 2 ^ (a + 1) * n = 2 * (2 ^ a * n) by ring,
      T_two_mul, ih]

/-- **Corollary 7.4 [`cor:conservation`]**, (7.3, `eq:conservation`): `I_n = {a ≥ 1 : 2^a n ≡ 1 (3)}`,
`m_a = (2^a n - 1)/3`; the series is a `HasSum` over `a ∈ ℕ`, zero off `I_n`. -/
theorem conservation (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∀ n : ℕ, 0 < n → Odd n → ¬ IsPeriodic n →
      HasSum (fun a : ℕ => if 1 ≤ a ∧ 2 ^ a * n % 3 = 1 then hpot ((2 ^ a * n - 1) / 3) else 0)
        (hpot n)) ∧
    ∀ n : ℕ, 0 < n → Tendsto (fun A : ℕ => hpot (2 ^ A * n)) atTop (𝓝 0) := by
  -- the dyadic ray `2^A n`
  have hray : ∀ n : ℕ, 0 < n → Tendsto (fun A : ℕ => hpot (2 ^ A * n)) atTop (𝓝 0) := by
    intro n hn
    refine raydecay hTM hTP hθ (fun A => 2 ^ A * n) (fun A => Nat.mul_pos (by positivity) hn)
      (fun a b hab => ?_) (fun A => ?_)
    · exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hn hab)
    · rw [show 2 ^ (A + 1) * n = 2 * (2 ^ A * n) by ring, T_two_mul]
  refine ⟨fun n hn hodd hper => ?_, hray⟩
  set f : ℕ → ℝ := fun a => if 1 ≤ a ∧ 2 ^ a * n % 3 = 1 then hpot ((2 ^ a * n - 1) / 3) else 0
    with hf
  -- every `2^a n` is nonperiodic
  have hnp : ∀ a, ¬ IsPeriodic (2 ^ a * n) := by
    rintro a ⟨p, hp, hpa⟩
    refine hper ⟨p, hp, ?_⟩
    calc T^[p] n = T^[p] (T^[a] (2 ^ a * n)) := by rw [iterate_two_pow_mul]
      _ = T^[a] (T^[p] (2 ^ a * n)) := by
          rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply]
      _ = n := by rw [hpa, iterate_two_pow_mul]
  -- one step of (7.2)
  have hstep1 : ∀ a, hpot (2 ^ a * n) = hpot (2 ^ (a + 1) * n) + f a := by
    intro a
    have h := flow_density hTM hTP hθ (n := 2 ^ a * n) (Nat.mul_pos (by positivity) hn) (hnp a)
    rw [show 2 * (2 ^ a * n) = 2 ^ (a + 1) * n by ring] at h
    rw [h]
    simp only [hf]
    congr 1
    have hcond : (2 ^ a * n) % 6 = 4 ↔ (1 ≤ a ∧ 2 ^ a * n % 3 = 1) := by
      obtain ⟨q, hq⟩ := hodd
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp only [pow_zero, one_mul, nonpos_iff_eq_zero, one_ne_zero, false_and, iff_false]
        omega
      · have hev : 2 ∣ 2 ^ a * n := Dvd.dvd.mul_right (dvd_pow_self 2 ha.ne') n
        generalize 2 ^ a * n = m at hev ⊢
        omega
    by_cases h6 : (2 ^ a * n) % 6 = 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h6), ite_eq_left_of_eq_true _ _ (eq_true (hcond.mp h6))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h6), ite_eq_right_of_eq_false _ _ (eq_false (mt hcond.mpr h6))]
  -- telescoping
  have htel : ∀ A, hpot n = hpot (2 ^ A * n) + ∑ a ∈ range A, f a := by
    intro A
    induction A with
    | zero => simp
    | succ A ih => rw [Finset.sum_range_succ, ih, hstep1 A]; ring
  have hfnn : ∀ a, 0 ≤ f a := fun a => by
    simp only [hf]
    split_ifs
    · exact hpot_nonneg hTM hTP hθ _
    · exact le_rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg hfnn]
  have hlim : Tendsto (fun A => hpot n - hpot (2 ^ A * n)) atTop (𝓝 (hpot n - 0)) :=
    tendsto_const_nhds.sub (hray n hn)
  rw [sub_zero] at hlim
  refine hlim.congr fun A => ?_
  have := htel A
  linarith

end CollatzCLT
