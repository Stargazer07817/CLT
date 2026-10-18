import LeanClt.Potential.Densities
import LeanClt.Main.OddBridge

/-!
# §7.1: odd sources and even targets

The optional statement `hpot_odd` of the checkpoint-17 plan. For every `n ≥ 1`, the even and odd
parts of `P_T(n)` each have density `h(n)/2`, and the proportion of `P_T(n)` among the odd integers
of `[Y, 2Y]` tends to `h(n)`: the relative density of `P_T(n)` among odd integers is `h(n)`.

* **The even part** agrees with `2 · P_T(n)` up to the single point `n`
  (`two_mul_mem_predT_iff`): if `2k ∈ P_T(n)` and `2k ≠ n` then `k ∈ P_T(n)`, and `k ∈ P_T(n)`
  gives `2k ∈ P_T(n)`. So its count up to `X` is within `1` of `#(P_T(n) ∩ [1, ⌊X/2⌋])`, and
  `tendsto_window_div_pow` gives `h(n)/2`.
* **The odd part** is the complement in `P_T(n)`, of density `h(n) - h(n)/2`.
* **The odd dyadic proportion** tends to `h(n)` by the chain estimate at a base
  (`density_near_base_of_tao` for the basin of `{n}`).

Nothing in the formalization of §7 depends on this file: Propositions 7.2 and 7.5 use natural
densities directly.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

open Classical in
/-- §7.1: the even and odd parts of `P_T(n)` each have density `h(n)/2`; the odd dyadic proportion
(`N_Y` uniform on `oddClosed Y`) tends to `h(n)`. -/
theorem hpot_odd (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (n : ℕ) (hn : 0 < n) :
    HasDensity {m | m ∈ Pred T n ∧ Even m} (hpot n / 2) ∧
    HasDensity {m | m ∈ Pred T n ∧ Odd m} (hpot n / 2) ∧
    Tendsto (fun Y : ℝ => (((oddClosed Y).filter (· ∈ Pred T n)).card : ℝ) / (oddClosed Y).card)
      atTop (𝓝 (hpot n)) := by
  have hP := hasDensity_hpot hTM hTP hθ n hn
  set E : Set ℕ := {m | m ∈ Pred T n ∧ Even m} with hE
  -- the even part against `2 · P_T(n)`, window by window
  have hlow : ∀ X, (window (Pred T n) (X / 2)).card ≤ (window E X).card := by
    intro X
    refine Finset.card_le_card_of_injOn (fun k => 2 * k) (fun k hk => ?_)
      (fun a _ b _ h => by simp only at h; omega)
    rw [Finset.mem_coe, mem_window] at hk ⊢
    beta_reduce
    obtain ⟨⟨h1, h2⟩, hkA⟩ := hk
    refine ⟨⟨by omega, by omega⟩, ?_, even_two_mul k⟩
    by_cases h2k : 2 * k = n
    · rw [h2k]; exact ⟨hn, 0, rfl⟩
    · exact (two_mul_mem_predT_iff (by omega) h2k).mpr hkA
  have hup : ∀ X, (window E X).card ≤ (window (Pred T n) (X / 2)).card + 1 := by
    intro X
    have hsub : window E X ⊆ (window (Pred T n) (X / 2)).image (fun k => 2 * k) ∪ {n} := by
      intro m hm
      rw [mem_window] at hm
      obtain ⟨⟨h1, h2⟩, hmA, hev⟩ := hm
      by_cases hmn : m = n
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hmn)
      · obtain ⟨k, rfl⟩ := hev
        refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, ?_, by ring⟩)
        rw [mem_window]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        refine (two_mul_mem_predT_iff (by omega) (by omega : 2 * k ≠ n)).mp ?_
        rwa [two_mul]
    calc (window E X).card
        ≤ ((window (Pred T n) (X / 2)).image (fun k => 2 * k) ∪ {n}).card := card_le_card hsub
      _ ≤ ((window (Pred T n) (X / 2)).image (fun k => 2 * k)).card + ({n} : Finset ℕ).card :=
          card_union_le _ _
      _ ≤ (window (Pred T n) (X / 2)).card + 1 := by
          rw [Finset.card_singleton]; exact Nat.add_le_add_right card_image_le 1
  -- the even part has density `h(n)/2`
  have hEd : HasDensity E (hpot n / 2) := by
    have h1 := tendsto_window_div_pow hP 1
    simp only [pow_one] at h1
    have h2 : Tendsto (fun X : ℕ => (((window (Pred T n) (X / 2)).card : ℝ) + 1) / X) atTop
        (𝓝 (hpot n * (1 / 2))) := by
      have h0 : Tendsto (fun X : ℕ => (1 : ℝ) / X) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      simpa [add_div] using h1.add h0
    have hl : ∀ X : ℕ, ((window (Pred T n) (X / 2)).card : ℝ) / X ≤ ((window E X).card : ℝ) / X :=
      fun X => div_le_div_of_nonneg_right (Nat.cast_le.mpr (hlow X)) (Nat.cast_nonneg _)
    have hu : ∀ X : ℕ,
        ((window E X).card : ℝ) / X ≤ (((window (Pred T n) (X / 2)).card : ℝ) + 1) / X :=
      fun X => div_le_div_of_nonneg_right (by exact_mod_cast hup X) (Nat.cast_nonneg _)
    have hsq := tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 hl hu
    unfold HasDensity
    convert hsq using 2
    ring
  -- the odd part is the complement in `P_T(n)`
  have hOd : HasDensity {m | m ∈ Pred T n ∧ Odd m} (hpot n / 2) := by
    have hdiff := HasDensity.diff (fun m hm => hm.1) hEd hP
    have hset : Pred T n \ E = {m | m ∈ Pred T n ∧ Odd m} := by
      ext m
      simp only [hE, Set.mem_sdiff, Set.mem_ofPred_eq, not_and, Nat.not_even_iff_odd]
      tauto
    rw [hset, show hpot n - hpot n / 2 = hpot n / 2 by ring] at hdiff
    exact hdiff
  refine ⟨hEd, hOd, ?_⟩
  -- the odd dyadic proportion, by the chain estimate at a base
  obtain ⟨δ, C, x₁, hδ, -, -, hdens⟩ := density_near_base_of_tao hTM hTP hθ 1 1
  have htr : Transport (Pred T n) (fun m => -(entry {n} m : ℝ)) 1 1 n := by
    rw [pred_eq_reach]
    exact transport_reach (fun m hm => by rw [Set.mem_singleton_iff.mp hm])
  have hdb : DoublingCompatible (Pred T n) (fun m => -(entry {n} m : ℝ)) 1 := by
    rw [pred_eq_reach]
    exact doubling_reach (n0 := n + 1) (by omega) (fun m hm h => by
      rw [Set.mem_singleton_iff] at h; omega)
  obtain ⟨p, hp, hbase⟩ := hdens (Pred T n) _ n 1 htr hdb
  have hpeq : p = hpot n := hp.unique hP
  have hg : Tendsto (fun B : ℝ => C * Real.log B ^ (-δ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop).const_mul C
    simpa using this
  rw [← hpeq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub hg) (by simpa using tendsto_const_nhds.add hg) ?_ ?_
  · filter_upwards [eventually_ge_atTop ((max x₁ n) ^ alpha)] with B hB
    have := abs_le.mp (hbase B hB)
    rw [oddCF_zero_re] at this
    linarith
  · filter_upwards [eventually_ge_atTop ((max x₁ n) ^ alpha)] with B hB
    have := abs_le.mp (hbase B hB)
    rw [oddCF_zero_re] at this
    linarith

end CollatzCLT
