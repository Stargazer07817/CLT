import LeanClt.Potential.Approx
import LeanClt.Potential.FlowPeriodic

/-!
# Theorem 1.4 [`thm:potential`]: the predecessor-density potential

Stage 7 of the checkpoint-17 plan. `potential_of_tao` proves Theorem 1.4 from the results of §7; the
headline statement `potential` is in `LeanClt/Statements.lean`.

* The density `h(n)` exists for every `n ≥ 1` (`hasDensity_hpot`).
* `h(n) > 0` iff `3 ∤ n`: Theorem 8.1 [`thm:positivity`] (`Positivity.positivity_of_tao`) gives a
  positive lower density when `3 ∤ n`; when `3 ∣ n`, `P_T(n)` is the dyadic hair `{2^j n}`
  (`pred_of_three_dvd`), of density `0` (`hasDensity_dyadic`).
* (i) is `flow_density`, (ii) is `raydecay`, and (iii) is `approx` with `f_K = fK K` and the weights
  `ν_K({k})`, which are nonnegative (`nuK_prob`).
* (iv), `⇐`: if every orbit is eventually periodic, each forward orbit is finite
  (`fwdOrbit_finite_of_eventually_periodic`), so `f_K` vanishes off a finite set and
  `h ≤ C (log K)^{-ε}` there. `⇒`: an orbit that is not eventually periodic is nonrepeating; along it
  `h(a_j) → π_C > 0` (`ray_densities`, from Theorems 1.3(iii) and 6.7), while `a_j → ∞`.

The "more precisely, `limsup h = sup π_C`" paragraph of v8's proof is not part of the theorem and is
not formalized.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-- The forward orbit of an eventually periodic point is finite. -/
lemma fwdOrbit_finite_of_eventually_periodic {k : ℕ} (h : ∃ i, IsPeriodic (T^[i] k)) :
    (fwdOrbit k).Finite := by
  obtain ⟨i, p, hp, hcyc⟩ := h
  refine ((range (i + p)).image (fun j => T^[j] k)).finite_toSet.subset ?_
  rintro x ⟨j, rfl⟩
  rw [Finset.mem_coe, Finset.mem_image]
  by_cases hj : j < i
  · exact ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  · refine ⟨i + (j - i) % p, Finset.mem_range.mpr (by have := Nat.mod_lt (j - i) hp; omega), ?_⟩
    have h1 : T^[j] k = T^[j - i] (T^[i] k) := by
      rw [← Function.iterate_add_apply, show j - i + i = j by omega]
    change T^[i + (j - i) % p] k = T^[j] k
    rw [h1, cycle_iter_mod hcyc (j - i), ← Function.iterate_add_apply, Nat.add_comm ((j - i) % p) i]

/-- An orbit that is not eventually periodic is nonrepeating. -/
lemma nonRepeating_of_not_eventually_periodic {a : ℕ} (h : ¬ ∃ i, IsPeriodic (T^[i] a)) :
    NonRepeating a := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h ⟨i, j - i, by omega, by
      simp only at hij
      rw [← Function.iterate_add_apply, show j - i + i = j by omega, ← hij]⟩
  · exact h ⟨j, i - j, by omega, by
      simp only at hij
      rw [← Function.iterate_add_apply, show i - j + j = i by omega, hij]⟩

/-- **Theorem 1.4 [`thm:potential`]**, from Tao's imports and Rhin's measure; restated verbatim as
`potential` in `LeanClt/Statements.lean`. -/
theorem potential_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∀ n : ℕ, 0 < n → HasDensity (Pred T n) (hpot n)) ∧
    (∀ n : ℕ, 0 < n → (0 < hpot n ↔ ¬ 3 ∣ n)) ∧
    (∀ n : ℕ, 0 < n → ¬ IsPeriodic n →
      hpot n = hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0)) ∧
    (∀ v : ℕ → ℕ, (∀ j, 0 < v j) → Function.Injective v → (∀ j, T (v (j + 1)) = v j) →
      Tendsto (fun j => hpot (v j)) atTop (𝓝 0)) ∧
    (∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ K : ℕ, 2 ≤ K → ∃ f : ℕ → ℝ,
      (∃ w : ℕ → ℝ, ∀ n, f n =
        ∑ k ∈ (range (K + 1)).filter Odd, w k * (fwdOrbit k).indicator (fun _ => (1 : ℝ)) n) ∧
      (∀ n, 0 ≤ f n) ∧
      ∀ n : ℕ, 0 < n → 0 ≤ hpot n - f n ∧ hpot n - f n ≤ C * (Real.log K) ^ (-ε)) ∧
    (Tendsto hpot atTop (𝓝 0) ↔ ∀ n : ℕ, 0 < n → ∃ i, IsPeriodic (T^[i] n)) := by
  classical
  have hdens := hasDensity_hpot hTM hTP hθ
  obtain ⟨C, ε, hC, hε, happ⟩ := approx hTM hTP hθ
  -- `f_K ≥ 0`
  have hfK : ∀ K n, 0 ≤ fK K n := by
    intro K n
    obtain ⟨hν0, -, -⟩ := nuK_prob hTM hTP hθ K
    unfold fK
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hν0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  refine ⟨hdens, fun n hn => ?_, fun n hn hper => flow_density hTM hTP hθ hn hper,
    fun v hv hinj hstep => raydecay hTM hTP hθ v hv hinj hstep,
    ⟨C, ε, hC, hε, fun K hK => ⟨fK K, ⟨fun k => nuK K {some k}, fun n => rfl⟩, hfK K,
      (happ K hK).1⟩⟩, ?_⟩
  · -- positivity iff `3 ∤ n`
    constructor
    · intro hpos h3
      have h0 : HasDensity (Pred T n) 0 := by
        rw [pred_of_three_dvd hn h3]; exact hasDensity_dyadic hn
      rw [(hdens n hn).unique h0] at hpos
      exact lt_irrefl _ hpos
    · intro h3
      obtain ⟨c, hc, hlow⟩ := Positivity.positivity_of_tao hTM hTP hn h3
      have hge : c ≤ hpot n := by
        refine ge_of_tendsto (hdens n hn) ?_
        filter_upwards [hlow, eventually_gt_atTop 0] with X hX hX0
        rw [le_div_iff₀ (by exact_mod_cast hX0)]
        exact hX
      linarith
  · -- (iv)
    constructor
    · -- `h → 0` forces every orbit to be eventually periodic
      intro hlim n hn
      by_contra hno
      have hR := nonRepeating_of_not_eventually_periodic hno
      obtain ⟨pC, hpC, -, h, hh, -, hhlim, -⟩ := ray_densities hTM hTP hθ hn hR
      have heq : ∀ j, hpot (T^[j] n) = h j := fun j =>
        (hdens _ (iterate_T_pos hn j)).unique (hh j)
      have h1 : Tendsto (fun j => hpot (T^[j] n)) atTop (𝓝 0) :=
        hlim.comp (Function.Injective.nat_tendsto_atTop hR)
      simp only [heq] at h1
      exact hpC.ne' (tendsto_nhds_unique hhlim h1)
    · -- every orbit eventually periodic: `f_K` has finite support
      intro hall
      have hlim0 : Tendsto (fun K : ℕ => C * Real.log K ^ (-ε)) atTop (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop hε).comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
        simpa [Function.comp_def] using this
      rw [tendsto_order]
      refine ⟨fun a ha => Eventually.of_forall fun m => lt_of_lt_of_le ha
        (hpot_nonneg hTM hTP hθ m), fun a ha => ?_⟩
      obtain ⟨K, hKa, hK2⟩ := ((hlim0.eventually (gt_mem_nhds ha)).and
        (eventually_ge_atTop 2)).exists
      set F := (range (K + 1)).filter Odd with hF
      have hfin : (⋃ k ∈ F, fwdOrbit k).Finite :=
        Set.Finite.biUnion (Finset.finite_toSet _) fun k hk =>
          fwdOrbit_finite_of_eventually_periodic
            (hall k (by rw [Finset.mem_coe, hF, Finset.mem_filter] at hk; exact hk.2.pos))
      obtain ⟨M, hM⟩ := hfin.bddAbove
      filter_upwards [eventually_gt_atTop M] with m hm
      have hm0 : 0 < m := by omega
      have hzero : fK K m = 0 := by
        unfold fK
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnot : m ∉ fwdOrbit k := fun h =>
          absurd (hM (Set.mem_biUnion (x := k) (Finset.mem_coe.mpr hk) h)) (by omega)
        rw [Set.indicator_of_notMem hnot, mul_zero]
      have := ((happ K hK2).1 m hm0).2
      rw [hzero, sub_zero] at this
      linarith

end CollatzCLT
