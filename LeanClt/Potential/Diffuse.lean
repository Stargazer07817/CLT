import LeanClt.Potential.Densities
import LeanClt.Exceptional.Thresholds

/-!
# Lemma 7.1 [`lem:diffuse`]: the entrance law `ν_K` is uniformly diffuse

Stage 3 of the checkpoint-17 plan. There are `C, ε > 0` with `ν_K({k}) ≤ C (log K)^{-ε}` for every
odd `k ≤ K` and for the cemetery `†`, for all `K ≥ 2`.

* **The cemetery.** `ν_K(†) = 1 - h_K` (`nuK_none`), and `h_K ≥ 1 - C₀ (log K)^{-δ₀}` is
  Theorem 1.3(i) [`thm:thresholds`] (`thresholds_i`).
* **An odd atom at the base `Y = K^α`** (`atom_count`). Sample `N` uniformly from the odd integers of
  `[K^α, 2K^α]`, with threshold `x = K`. By Lemma 5.1 [`lem:typical`] (`typical` with `A = 1`) at
  most `(log K)^{-1} L_Y` sources are atypical. A typical source crosses below `K` by time `n₀`
  (Lemma 5.2 [`lem:orbit`], `orbit_window`), so `H_K(N) = U^{T_K(N)}(N)` (`entK_eq_some_passT`), and
  its valuation total up to that time is at most `S_{n₀} ≤ 2n₀ + L^{0.6} ≤ 3n₀`. The set of partial
  sums `{S_1, …, S_{T_K(N)}} ⊆ [1, 3n₀]` determines the length and the word (`Swd_eq_of_psums`,
  through `Finset.orderEmbOfFin_unique`), and the word together with `H_K(N) = k` determines `N`
  (Lemma 2.1 [`lem:inverse`], `source_unique`). So at most `2^{3n₀} ≤ K^{0.3}` typical sources have
  `H_K(N) = k`, and `P(H_K(N_{K^α}) = k) ≤ 2 (log K)^{-1}` for all large `K`.
* **Transfer to `ν_K`.** The chain estimate at the base `B = K^α` (`nuK_base`, valid once
  `K ≥ x₁`) gives `ν_K({k}) ≤ 2 (log K)^{-1} + C (log K)^{-δ}`. On the bounded range of `K` every
  atom is at most `1`, which a larger constant absorbs.

The route differs from v8 in one respect: v8 uses Lemma 5.3 [`lem:failure`] with a linear Chernoff
bound, which gives a power saving `O(K^{-d})` for the bad event; Lemmas 5.1 and 5.2 give the
polylogarithmic saving `(log K)^{-1}`, which is all the lemma needs.
-/

open Real Filter Topology Finset

noncomputable section

namespace CollatzCLT

/-! ## Partial sums of a valuation word -/

/-- The set `{S_1, …, S_r}` of the first `r` partial sums of the valuation word of `N`. -/
def psums (N r : ℕ) : Finset ℕ := (range r).image (fun i => Swd N (i + 1))

lemma Swd_zero (N : ℕ) : Swd N 0 = 0 := by simp [Swd, wsum]

lemma Swd_succ (N i : ℕ) : Swd N (i + 1) = Swd N i + vword N i := by
  simp only [Swd, wsum, Finset.sum_range_succ]

lemma Swd_mono (N : ℕ) {i j : ℕ} (h : i ≤ j) : Swd N i ≤ Swd N j := by
  unfold Swd wsum
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma Swd_strictMono {N : ℕ} (hN : Odd N) : StrictMono (fun i => Swd N (i + 1)) := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  change Swd N (i + 1) < Swd N (i + 1 + 1)
  rw [Swd_succ N (i + 1)]
  have := vword_pos hN (i + 1)
  omega

lemma card_psums {N : ℕ} (hN : Odd N) (r : ℕ) : (psums N r).card = r := by
  unfold psums
  rw [Finset.card_image_of_injective _ (Swd_strictMono hN).injective, Finset.card_range]

/-- The partial-sum set of length `r` determines the first `r` partial sums. -/
lemma Swd_eq_of_psums {N N' r : ℕ} (hN : Odd N) (hN' : Odd N') (h : psums N r = psums N' r) :
    ∀ i ≤ r, Swd N i = Swd N' i := by
  have hc : (psums N r).card = r := card_psums hN r
  have hf := Finset.orderEmbOfFin_unique hc (f := fun j : Fin r => Swd N (j + 1))
    (fun j => Finset.mem_image_of_mem _ (Finset.mem_range.mpr j.2))
    (fun a b hab => Swd_strictMono hN hab)
  have hg := Finset.orderEmbOfFin_unique hc (f := fun j : Fin r => Swd N' (j + 1))
    (fun j => by rw [h]; exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr j.2))
    (fun a b hab => Swd_strictMono hN' hab)
  intro i hi
  rcases i with _ | i
  · simp [Swd_zero]
  · exact congrFun (hf.trans hg.symm) ⟨i, by omega⟩

/-- The partial-sum set of length `r` determines the first `r` letters. -/
lemma vword_eq_of_psums {N N' r : ℕ} (hN : Odd N) (hN' : Odd N') (h : psums N r = psums N' r) :
    ∀ i < r, vword N i = vword N' i := by
  have hS := Swd_eq_of_psums hN hN' h
  intro i hi
  have h1 := Swd_succ N i
  have h2 := Swd_succ N' i
  have h3 := hS i hi.le
  have h4 := hS (i + 1) hi
  omega

/-! ## The label of an odd source that crosses -/

/-- For odd `N` crossing below `K`, `H_K(N) = U^{T_K(N)}(N)`. -/
lemma entK_eq_some_passT {K N : ℕ} (hN : Odd N) (hc : crosses (K : ℝ) N) :
    entK K N = some (U^[passT K N] N) := by
  classical
  have h : ∃ r, U^[r] N ≤ K := by
    obtain ⟨r, hr⟩ := hc
    exact ⟨r, by exact_mod_cast hr⟩
  rw [entK_of_odd K hN, dite_eq_left_of_eq_true (eq_true h)]
  have hp : passT K N = Nat.find h := by
    refine le_antisymm (passT_le (by exact_mod_cast Nat.find_spec h)) (Nat.find_min' h ?_)
    exact_mod_cast passT_spec hc
  rw [hp]

/-! ## Numerical side conditions -/

lemma ev_count_numeric : ∀ᶠ x : ℝ in atTop, x ^ (0.3 : ℝ) * Real.log x + 3 / 2 ≤ x ^ alpha / 2 := by
  filter_upwards [ev_rpow_le_mul (a := 0.8) (ε := 1 / 8) (by norm_num) (by norm_num),
    eventually_ge_atTop (6 : ℝ)] with x h1 h2
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ (0.5 : ℝ) / 0.5 := Real.log_le_rpow_div hx0.le (by norm_num)
  have hprod : x ^ (0.3 : ℝ) * Real.log x ≤ 2 * x ^ (0.8 : ℝ) := by
    calc x ^ (0.3 : ℝ) * Real.log x ≤ x ^ (0.3 : ℝ) * (x ^ (0.5 : ℝ) / 0.5) := by
          gcongr
      _ = 2 * (x ^ (0.3 : ℝ) * x ^ (0.5 : ℝ)) := by ring
      _ = 2 * x ^ (0.8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
  have hxa : x ≤ x ^ alpha := Real.self_le_rpow_of_one_le (by linarith) (by unfold alpha; norm_num)
  linarith

lemma ev_n0_ge : ∀ᶠ x : ℝ in atTop, Lx x ^ (0.6 : ℝ) ≤ n0 x := by
  filter_upwards [ev_of_log ((ev_rpow_le_mul (a := 0.6) (ε := 1 / 20) (by norm_num)
    (by norm_num)).and (eventually_ge_atTop (20 : ℝ)))] with x hx
  obtain ⟨h1, h2⟩ := hx
  have h3 := n0_ge x
  have hl := ell_pos
  have hl7 := ell_lt_07
  have h4 : Lx x / 7 ≤ Lx x / (10 * ell) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  linarith

lemma two_pow_le_rpow {x : ℝ} (hx : 1 ≤ Lx x) (hx0 : 0 < x) :
    (2 : ℝ) ^ (3 * n0 x) ≤ x ^ (0.3 : ℝ) := by
  have hn := n0_le x hx
  have hl := ell_pos
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have : (3 * n0 x : ℕ) * Real.log 2 ≤ 3 * (Lx x / (10 * ell)) * ell := by
    change (3 * n0 x : ℕ) * ell ≤ 3 * (Lx x / (10 * ell)) * ell
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hn hl.le]
  have e : 3 * (Lx x / (10 * ell)) * ell = Real.log x * 0.3 := by
    unfold Lx; field_simp; ring
  linarith

/-! ## An odd atom at the base `Y = K^α` -/

open Classical in
/-- **The sources of one atom.** For all large `K` and every `k`,
`P(H_K(N_{K^α}) = k) ≤ 2 (log K)^{-1}`. -/
theorem atom_count : ∀ᶠ K : ℕ in atTop, ∀ k : ℕ,
    lawHK K ((K : ℝ) ^ alpha) {some k} ≤ 2 * (Real.log K) ^ (-(1 : ℝ)) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (large_ev.and ((typical 1).and (ev_count_numeric.and ev_n0_ge)))] with K hK k
  obtain ⟨hL, htyp, hnum, hn0⟩ := hK
  set x : ℝ := (K : ℝ) with hxdef
  set Y : ℝ := x ^ alpha with hYdef
  have hY1 : x ^ alpha ≤ Y := le_rfl
  have hx1 : 1 < x := hL.x_gt
  have hY2 : Y ≤ x ^ (alpha ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by unfold alpha; norm_num)
  obtain ⟨hx0, h2e5, hxY, hY0⟩ := large_facts hL hY1
  have hLYpos : (0 : ℝ) < LY Y := LY_pos (by linarith)
  have hLx1 : 1 ≤ Lx x := le_trans (by norm_num) hL.L_ge
  set S := (oddClosed Y).filter (fun N => entK K N = some k) with hS
  set G := S.filter (fun N => Good x N) with hG
  -- the atypical sources
  have hbad : ((S.filter (fun N => ¬ Good x N)).card : ℝ) ≤ Lx x ^ (-(1 : ℝ)) * LY Y := by
    refine le_trans ?_ (htyp Y hY1)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  -- facts about a typical source of the atom
  have hfacts : ∀ N ∈ G, Odd N ∧ U^[passT x N] N = k ∧ Swd N (passT x N) ≤ 3 * n0 x := by
    intro N hN
    rw [hG, Finset.mem_filter, hS, Finset.mem_filter] at hN
    obtain ⟨⟨hNY, hNk⟩, hGood⟩ := hN
    obtain ⟨hNo, -, -⟩ := mem_oddClosed hY0.le hNY
    obtain ⟨hcr, -, hle, -⟩ := orbit_window hL hY1 hY2 hNY hGood
    have hsome := entK_eq_some_passT hNo hcr
    rw [hsome, Option.some.injEq] at hNk
    refine ⟨hNo, hNk, ?_⟩
    have hG0 := (abs_le.mp (hGood (n0 x) le_rfl)).2
    have h3 : (Swd N (n0 x) : ℝ) ≤ 3 * n0 x := by linarith
    have h3' : Swd N (n0 x) ≤ 3 * n0 x := by exact_mod_cast h3
    exact (Swd_mono N hle).trans h3'
  -- the typical sources, through their partial-sum sets
  have hgood : G.card ≤ 2 ^ (3 * n0 x) := by
    have hmaps : Set.MapsTo (fun N => psums N (passT x N)) G
        (Finset.Icc 1 (3 * n0 x)).powerset := by
      intro N hN
      obtain ⟨hNo, -, hSw⟩ := hfacts N hN
      simp only [Finset.mem_coe, Finset.mem_powerset]
      intro m hm
      simp only [psums, Finset.mem_image, Finset.mem_range] at hm
      obtain ⟨i, hi, rfl⟩ := hm
      rw [Finset.mem_Icc]
      exact ⟨wsum_pos (vword_pos hNo) (by omega), (Swd_mono N (by omega)).trans hSw⟩
    have hinj : Set.InjOn (fun N => psums N (passT x N)) G := by
      intro N hN N' hN' heq
      obtain ⟨hNo, hNk, -⟩ := hfacts N hN
      obtain ⟨hNo', hNk', -⟩ := hfacts N' hN'
      have hr : passT x N = passT x N' := by
        have := congrArg Finset.card heq
        simp only at this
        rwa [card_psums hNo, card_psums hNo'] at this
      simp only at heq
      rw [← hr] at heq hNk'
      exact source_unique (vword_eq_of_psums hNo hNo' heq) (hNk.trans hNk'.symm)
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    rwa [Finset.card_powerset, Nat.card_Icc, Nat.add_sub_cancel] at this
  -- assembling the count
  have hsplit : (S.card : ℝ) = G.card + (S.filter (fun N => ¬ Good x N)).card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (fun N => Good x N)).symm
  have hpow : ((2 ^ (3 * n0 x) : ℕ) : ℝ) ≤ x ^ (0.3 : ℝ) := by
    push_cast; exact two_pow_le_rpow hLx1 hx0
  have hLx0 : 0 < Lx x := by linarith
  have hrp : Lx x ^ (-(1 : ℝ)) = (Lx x)⁻¹ := Real.rpow_neg_one _
  have hLYge := LY_ge hY0.le
  have hsmall : x ^ (0.3 : ℝ) ≤ Lx x ^ (-(1 : ℝ)) * LY Y := by
    rw [hrp, inv_mul_eq_div, le_div_iff₀ hLx0]
    have : x ^ (0.3 : ℝ) * Lx x + 3 / 2 ≤ Y / 2 := hnum
    linarith
  have hScard : (S.card : ℝ) ≤ 2 * Lx x ^ (-(1 : ℝ)) * LY Y := by
    have hg : (G.card : ℝ) ≤ ((2 ^ (3 * n0 x) : ℕ) : ℝ) := by exact_mod_cast hgood
    linarith
  have hlaw : lawHK K Y {some k} = S.card / LY Y := by
    unfold lawHK LY
    congr 3
    ext N
    simp [hS]
  rw [hlaw, div_le_iff₀ hLYpos]
  have : Lx x = Real.log K := rfl
  rw [← this]
  linarith

/-! ## Lemma 7.1 -/

/-- **Lemma 7.1 [`lem:diffuse`].** -/
theorem diffuse (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ K : ℕ, 2 ≤ K →
      nuK K {none} ≤ C * (Real.log K) ^ (-ε) ∧
      ∀ k : ℕ, Odd k → k ≤ K → nuK K {some k} ≤ C * (Real.log K) ^ (-ε) := by
  obtain ⟨-, C0, δ0, hC0, hδ0, hlow⟩ := thresholds_i hTM hTP hθ
  obtain ⟨δ, C, x₁, hδ, hC, hx₁, hb⟩ := nuK_base hTM hTP hθ
  obtain ⟨K1, hK1⟩ := eventually_atTop.mp atom_count
  set K2 : ℕ := max (max K1 ⌈x₁⌉₊) 3 with hK2
  set ε := min (min δ0 δ) 1 with hε
  have hεpos : 0 < ε := lt_min (lt_min hδ0 hδ) one_pos
  have hK23 : 3 ≤ K2 := le_max_right _ _
  have hlogK2 : 0 < Real.log K2 := Real.log_pos (by exact_mod_cast (by omega : 1 < K2))
  set Cf := max (C0 + 2 + C) ((Real.log K2) ^ ε) with hCf
  have hCfpos : 0 < Cf := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨Cf, ε, hCfpos, hεpos, fun K hK => ?_⟩
  have hle1 : ∀ e, nuK K {e} ≤ 1 := fun e =>
    le_of_tendsto' (nuK_tendsto hTM hTP hθ K {e}) (fun Y => lawHK_le_one K Y {e})
  have hlogK : 0 < Real.log K := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  by_cases hsmall : K < K2
  · -- the bounded range: every atom is at most `1`
    have hpow : (Real.log K2) ^ (-ε) ≤ (Real.log K) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos hlogK
        (Real.log_le_log (by positivity) (by exact_mod_cast hsmall.le)) (by linarith)
    have hone : 1 ≤ Cf * (Real.log K) ^ (-ε) := by
      have e : (Real.log K2) ^ ε * (Real.log K2) ^ (-ε) = 1 := by
        rw [← Real.rpow_add hlogK2]; simp
      calc (1 : ℝ) = (Real.log K2) ^ ε * (Real.log K2) ^ (-ε) := e.symm
        _ ≤ Cf * (Real.log K) ^ (-ε) :=
          mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg hlogK2.le _) hCfpos.le
    exact ⟨(hle1 none).trans hone, fun k _ _ => (hle1 (some k)).trans hone⟩
  · push Not at hsmall
    have hKK1 : K1 ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall
    have hKx : x₁ ≤ (K : ℝ) := by
      have h1 : x₁ ≤ (⌈x₁⌉₊ : ℝ) := Nat.le_ceil x₁
      have h2 : ⌈x₁⌉₊ ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall
      exact h1.trans (by exact_mod_cast h2)
    have hK3 : 3 ≤ K := le_trans hK23 hsmall
    have hlogK1 : 1 ≤ Real.log K := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      have h3 : (3 : ℝ) ≤ K := by exact_mod_cast hK3
      linarith
    have hmono : ∀ a, ε ≤ a → (Real.log K) ^ (-a) ≤ (Real.log K) ^ (-ε) :=
      fun a ha => Real.rpow_le_rpow_of_exponent_le hlogK1 (by linarith)
    have hrpow : 0 ≤ (Real.log K) ^ (-ε) := Real.rpow_nonneg hlogK.le _
    have hCf1 : C0 + 2 + C ≤ Cf := le_max_left _ _
    constructor
    · -- the cemetery: `ν_K(†) = 1 - h_K` and Theorem 1.3(i)
      have hAK := nuK_none hTM hTP hθ K (by omega)
      have h1 := hlow K hK _ hAK
      have h2 : nuK K {none} ≤ C0 * (Real.log K) ^ (-δ0) := by linarith
      have h3 : C0 * (Real.log K) ^ (-δ0) ≤ C0 * (Real.log K) ^ (-ε) :=
        mul_le_mul_of_nonneg_left (hmono δ0 ((min_le_left _ _).trans (min_le_left _ _))) hC0.le
      have h4 : C0 * (Real.log K) ^ (-ε) ≤ Cf * (Real.log K) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow
      linarith
    · -- an odd atom: the count at the base `K^α`, then the chain estimate
      intro k _ _
      have hcount := hK1 K hKK1 k
      have hbase := (hb K {some k}).2 ((K : ℝ) ^ alpha) (by rw [max_eq_right hKx])
      have hlogα : Real.log K ≤ Real.log ((K : ℝ) ^ alpha) := by
        rw [Real.log_rpow (by positivity)]
        have : (1 : ℝ) ≤ alpha := by unfold alpha; norm_num
        nlinarith
      have hpowα : Real.log ((K : ℝ) ^ alpha) ^ (-δ) ≤ Real.log K ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hlogK hlogα (by linarith)
      have h1 : nuK K {some k} ≤ 2 * (Real.log K) ^ (-(1 : ℝ)) + C * (Real.log K) ^ (-δ) := by
        have h := (abs_le.mp hbase).2
        have h' : C * Real.log ((K : ℝ) ^ alpha) ^ (-δ) ≤ C * Real.log K ^ (-δ) :=
          mul_le_mul_of_nonneg_left hpowα hC
        linarith
      have h2 : 2 * (Real.log K) ^ (-(1 : ℝ)) ≤ 2 * (Real.log K) ^ (-ε) :=
        mul_le_mul_of_nonneg_left (hmono 1 (min_le_right _ _)) (by norm_num)
      have h3 : C * (Real.log K) ^ (-δ) ≤ C * (Real.log K) ^ (-ε) :=
        mul_le_mul_of_nonneg_left (hmono δ ((min_le_left _ _).trans (min_le_right _ _))) hC
      have h4 : (2 + C) * (Real.log K) ^ (-ε) ≤ Cf * (Real.log K) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow
      nlinarith

end CollatzCLT
