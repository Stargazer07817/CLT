import LeanClt.Sampling.Lemma64
import LeanClt.Applications.PinnedTransfer
import LeanClt.Renewal.FixedFreq
import LeanClt.Transfer.Transport
import LeanClt.Main.Conditional

/-!
# Theorem 6.13 [`thm:modq`]: equidistribution of the clocks modulo `Q₀` (stage 8 of the
checkpoint-20 plan)

The two sampling lemmas and the Fourier inversion are unconditional; the decay at a nonzero
frequency and Theorem 6.13 use `TaoMajorant`, `TaoPrefix` and `IrrMeasure`.

* **Lemma 6.5 [`lem:sampling`] at a fixed frequency.** `uniform_of_odd_dyadic_fixed`: if the odd
  dyadic phase average `E[1_A(N_Y) e^{isq(N_Y)}]` tends to `0` at a fixed `s` and `(A, q)` is
  doubling compatible, the average over `[1, X]` tends to `0`. The proof is that of
  `uniform_limit` with `κ = 0` and the limit `0`: split `n = 2^e u` (`sum_Icc_two_adic`), then
  `u` into dyadic blocks (`dyadic_tannery`). On a block, doubling turns `2^e u` into `u` at the
  cost of the constant phase `e^{-ise·e₀}` (`DoublingCompatible.iterate`, `ph_two_pow_mul`), which
  has modulus `1` and need not tend to `1`, because the limit is `0` (`block_limit_fixed`).
  `uniform_of_odd_dyadic_fixed_odd` is the version for a set of odd integers, where only the
  layer `e = 0` contributes and no doubling is needed.
* **Decay at a nonzero frequency.** `phi0_tendsto_zero`: for a transported clock with coprime
  integer reward, `E[1_A(N_Y) e^{isq(N_Y)}] → 0` at `s = 2πr/Q₀`, `0 < r < Q₀`. Write `r/Q₀` in
  lowest terms `r'/Q'`, `Q' ≥ 2` (`exists_lowest_terms`); Proposition 4.5 [`prop:fixedfreq`]
  bounds the kernel by `C u^{-a} log u`, `a = 1/(2(ϰ+1))`, and `u^{-a} log u ≤ (2/a) v^{-a/2}`
  for `u ≥ v` (`rpow_neg_mul_log_le`), so `phi0_le_of_kernel` applies with
  `B = |C| (2/a) (c₀ log Y)^{-a/2} → 0`.
* **Finite Fourier inversion on `ZMod Q₀`.** `hasDensity_mod_of_phases`:
  `1{τ ≡ r₀} = Q₀⁻¹ ∑_{r<Q₀} e^{2πir(r₀ - τ)/Q₀}` (`sum_range_cexp_int`, by `geom_sum_eq` for a
  nontrivial root of unity); the term `r = 0` is the density `p` of `A`, the others tend to `0`.
* **Theorem 6.13** (`modq`): the three clocks, with the clock `q = -τ_{G,b}` on `P_G(b)`,
  `transport_T`, `transport_F`, `transport_U` at threshold `b + 1`, `doubling_T`, `doubling_F`,
  and odd sources for `G = U` (`P_U(b)` is odd).
-/

open Real Filter Topology Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Lemma 6.5 at a fixed frequency -/

section Sampling

variable {A : Set ℕ} {q : ℕ → ℝ} {e0 : ℝ}

/-- With centring `κ = 0` the odd dyadic characteristic function is `phi0`. -/
lemma oddCF_centre_zero (A : Set ℕ) (q : ℕ → ℝ) (Y s : ℝ) : oddCF A q 0 Y s = phi0 A q Y s := by
  unfold oddCF phi0 ph
  simp

/-- With centring `κ = 0` the clock phase is the plain phase `1_A(n) e^{isq(n)}`. -/
lemma ph_zero_mul (A : Set ℕ) (q : ℕ → ℝ) (s c : ℝ) (n : ℕ) :
    ph A q s (0 * c) n = A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) n := by
  unfold ph
  simp

/-- With centring `κ = 0` there is nothing to recentre. -/
lemma err2_zero (A : Set ℕ) (q : ℕ → ℝ) (s : ℝ) (W : ℕ) : err2 A q 0 s W = 0 := by
  unfold err2
  simp

/-- **Block limit at a fixed frequency.** For fixed `e` and `k` (with doubling compatibility at
that `e`), the sum over the `k`-th dyadic block of `[1, ⌊X/2^e⌋]` of the odd-part phases
`1_{u odd} 1_A(2^e u) e^{isq(2^e u)}`, divided by `⌊X/2^e⌋`, tends to `0` when the odd dyadic
phase average does. -/
theorem block_limit_fixed (s : ℝ) (hodd : Tendsto (fun Y : ℝ => phi0 A q Y s) atTop (𝓝 0))
    (e k : ℕ)
    (hdble : ∃ n0 : ℕ, ∀ u : ℕ, n0 ≤ u →
      (2 ^ e * u ∈ A ↔ u ∈ A) ∧ (u ∈ A → q (2 ^ e * u) = q u - e * e0)) :
    Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℂ)⁻¹ *
      ∑ u ∈ Ioc ((X / 2 ^ e) / 2 ^ (k + 1)) ((X / 2 ^ e) / 2 ^ k),
        (if Odd u then ph A q s (0 * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) else 0))
      atTop (𝓝 0) := by
  classical
  obtain ⟨n0, hn0⟩ := hdble
  have hmpos : 0 < 2 ^ (e + k + 1) := by positivity
  have he0 : 0 < 2 ^ e := by positivity
  have hZW : ∀ X : ℕ, X / 2 ^ e / 2 ^ (k + 1) = X / 2 ^ (e + k + 1) := by
    intro X; rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
  -- (a) the odd dyadic phase average at scale `W = ⌊X/2^{e+k+1}⌋` tends to `0`
  have hcf : Tendsto (fun X : ℕ => oddCF A q 0 ((X / 2 ^ (e + k + 1) : ℕ) : ℝ) s) atTop
      (𝓝 0) := by
    simp only [oddCF_centre_zero]
    exact hodd.comp (tendsto_natCast_atTop_atTop.comp (tendsto_natDiv_atTop hmpos))
  -- (b) `#oddClosed(W) / Z → 1/2^{k+2}`, with `Z = ⌊X/2^e⌋`
  have hWX := tendsto_natDiv_div_self hmpos
  have hZX : Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2 ^ e)) := by
    simpa using tendsto_natDiv_div_self he0
  have hcX : Tendsto (fun X : ℕ => ((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℝ) / X)
      atTop (𝓝 (1 / 2 ^ (e + k + 2))) := by
    have hlo : Tendsto (fun X : ℕ => (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / X) / 2) atTop
        (𝓝 (1 / 2 ^ (e + k + 2))) := by
      have := hWX.div_const 2
      convert this using 2
      push_cast; rw [pow_succ]; field_simp
    have hhi : Tendsto (fun X : ℕ => (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / X) / 2 + 1 / X) atTop
        (𝓝 (1 / 2 ^ (e + k + 2))) := by
      simpa using hlo.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1))] with X hX
      have hW1 : 1 ≤ X / 2 ^ (e + k + 1) := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa using hX)
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le hmpos hX)
      have hb := (card_oddClosed_bounds hW1).1
      calc (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / X) / 2
          = (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / 2) / X := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hb hXpos.le
    · filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1))] with X hX
      have hW1 : 1 ≤ X / 2 ^ (e + k + 1) := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa using hX)
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le hmpos hX)
      have hb := (card_oddClosed_bounds hW1).2
      calc _ ≤ ((((X / 2 ^ (e + k + 1) : ℕ) : ℝ)) / 2 + 1) / X :=
            div_le_div_of_nonneg_right hb hXpos.le
        _ = _ := by ring
  have hcZ : Tendsto (fun X : ℕ => ((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℝ) /
      ((X / 2 ^ e : ℕ) : ℝ)) atTop (𝓝 (1 / 2 ^ (k + 2))) := by
    have := hcX.div hZX (by positivity)
    have hval : (1 : ℝ) / 2 ^ (e + k + 2) / (1 / 2 ^ e) = 1 / 2 ^ (k + 2) := by
      rw [show e + k + 2 = e + (k + 2) by ring, pow_add]; field_simp
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (2 ^ e)] with X hX
    have hZ1 : 1 ≤ X / 2 ^ e := (Nat.le_div_iff_mul_le he0).mpr (by simpa using hX)
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le he0 hX)
    have hZpos : (0 : ℝ) < ((X / 2 ^ e : ℕ) : ℝ) := by exact_mod_cast hZ1
    simp only [Pi.div_apply]
    field_simp
  -- (c) the endpoint error, normalised by `Z`; the recentring error vanishes (`κ = 0`)
  have hZtop : Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_natDiv_atTop he0)
  have hR1 : Tendsto (fun X : ℕ => (((X / 2 ^ e : ℕ) : ℂ))⁻¹ *
      err1 A q 0 s (X / 2 ^ (e + k + 1)) (X / 2 ^ e / 2 ^ k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun X => 2 / ((X / 2 ^ e : ℕ) : ℝ))
    · refine Eventually.of_forall fun X => ?_
      have h1 : 2 * (X / 2 ^ (e + k + 1)) ≤ X / 2 ^ e / 2 ^ k := by
        rw [← hZW]; exact (block_endpoints (X / 2 ^ e) k).1
      have h2 : X / 2 ^ e / 2 ^ k ≤ 2 * (X / 2 ^ (e + k + 1)) + 1 := by
        rw [← hZW]; exact (block_endpoints (X / 2 ^ e) k).2
      have hb := norm_sum_block_sub_oddClosed_le h1 h2
        (fun u => ph A q s (0 * Real.log u) u) (fun u => norm_ph_le _ _ _ _ _)
      rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      exact hb
    · simpa using (tendsto_const_nhds (x := (2 : ℝ))).div_atTop hZtop
  have hR2 : Tendsto (fun X : ℕ => (((X / 2 ^ e : ℕ) : ℂ))⁻¹ *
      err2 A q 0 s (X / 2 ^ (e + k + 1))) atTop (𝓝 0) := by
    simp only [err2_zero, mul_zero]
    exact tendsto_const_nhds
  -- (d) assemble: the constant phase `e^{-ise·e₀}` times a quantity tending to `0`
  have hlim := (tendsto_const_nhds
    (x := cexp (((s * (e * (0 * Real.log 2 - e0)) : ℝ) : ℂ) * I))).mul
    ((((Complex.continuous_ofReal.tendsto _).comp hcZ).mul hcf).add hR1 |>.add hR2)
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1) * (n0 + 1))] with X hX
  have hWn0 : n0 + 1 ≤ X / 2 ^ (e + k + 1) :=
    (Nat.le_div_iff_mul_le hmpos).mpr (by linarith [hX])
  have hcpos : ((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℂ) ≠ 0 := by
    have hb := (card_oddClosed_bounds (W := X / 2 ^ (e + k + 1)) (by omega)).1
    have hne : (oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card ≠ 0 := by
      intro h0
      have hW' : (0 : ℝ) < ((X / 2 ^ (e + k + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < X / 2 ^ (e + k + 1))
      rw [h0, Nat.cast_zero] at hb
      linarith
    exact_mod_cast hne
  -- rewrite the block sum
  have hfac : ∀ u ∈ (Ioc (X / 2 ^ (e + k + 1)) (X / 2 ^ e / 2 ^ k)).filter Odd,
      ph A q s (0 * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) =
      cexp (((s * (e * (0 * Real.log 2 - e0)) : ℝ) : ℂ) * I) *
        ph A q s (0 * Real.log u) u := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Ioc] at hu
    have h1 : X / 2 ^ (e + k + 1) < u := hu.1.1
    exact ph_two_pow_mul e hn0 s (by omega) (by omega)
  rw [hZW, ← sum_filter, sum_congr rfl hfac, ← mul_sum,
    block_sum_eq A q 0 s _ _ hcpos]
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **Lemma 6.5 [`lem:sampling`] at a fixed frequency** (proof of Theorem 6.13): if the odd dyadic
phase average tends to `0` and `(A, q)` is doubling compatible, so does the average over `[1, X]`. -/
theorem uniform_of_odd_dyadic_fixed {A : Set ℕ} {q : ℕ → ℝ} {e0 : ℝ}
    (hdbl : DoublingCompatible A q e0) (s : ℝ)
    (hodd : Tendsto (fun Y : ℝ => phi0 A q Y s) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => (X : ℂ)⁻¹ *
      ∑ n ∈ Icc 1 X, A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) n) atTop (𝓝 0) := by
  classical
  -- the `e`-th two-adic layer
  let T : ℕ → ℕ → ℂ := fun X e => (X : ℂ)⁻¹ *
    ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, ph A q s (0 * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u)
  have hconv : ∀ X : ℕ, ∑ n ∈ Icc 1 X, A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) n =
      ∑ n ∈ Icc 1 X, ph A q s (0 * Real.log n) n :=
    fun X => sum_congr rfl fun n _ => (ph_zero_mul A q s _ n).symm
  have hsum : ∀ X : ℕ, (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q s (0 * Real.log n) n = ∑' e, T X e := by
    intro X
    rw [tsum_eq_sum (s := range (X + 1)), sum_Icc_two_adic, mul_sum]
    intro e he
    simp only [mem_range, not_lt] at he
    have h0 : X / 2 ^ e = 0 :=
      Nat.div_eq_of_lt ((Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right two_pos (by omega)))
    simp [T, h0]
  -- each layer tends to `0`
  have hlayer : ∀ e : ℕ, Tendsto (fun X => T X e) atTop (𝓝 0) := by
    intro e
    have he0 : 0 < 2 ^ e := by positivity
    have hinner := dyadic_tannery (L := atTop) (Z := fun X : ℕ => X / 2 ^ e)
      (f := fun X u => if Odd u then
        ph A q s (0 * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) else 0)
      (fun X u => by split_ifs <;> simp [norm_ph_le])
      (ℓ := 0) (fun k => by
        obtain ⟨n0, hn0⟩ := hdbl.iterate
        simpa using block_limit_fixed s hodd e k ⟨n0, hn0 e⟩)
    have hZX : Tendsto (fun X : ℕ => ((((X / 2 ^ e : ℕ) : ℝ) / X : ℝ) : ℂ)) atTop
        (𝓝 (((1 / 2 ^ e : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (by simpa using tendsto_natDiv_div_self he0)
    have := hZX.mul hinner
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (2 ^ e)] with X hX
    have hZ1 : 1 ≤ X / 2 ^ e := (Nat.le_div_iff_mul_le he0).mpr (by simpa using hX)
    have hZpos : ((X / 2 ^ e : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : X / 2 ^ e ≠ 0)
    have hXpos : (X : ℂ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
    simp only [T, ← sum_filter]
    push_cast
    field_simp
  -- domination: `‖T X e‖ ≤ 2^{-e}`
  have hbound : ∀ X e, ‖T X e‖ ≤ (1 / 2 : ℝ) ^ e := by
    intro X e
    rcases Nat.eq_zero_or_pos X with hX | hX
    · simp [T, hX]
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    calc ‖T X e‖ ≤ ((X : ℝ))⁻¹ * ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, (1 : ℝ) := by
          simp only [T, norm_mul, norm_inv, Complex.norm_natCast]
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun u _ => norm_ph_le _ _ _ _ _)
      _ ≤ ((X : ℝ))⁻¹ * ((X / 2 ^ e : ℕ) : ℝ) := by
          gcongr
          simp only [sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast (card_filter_le _ _).trans (by simp)
      _ ≤ ((X : ℝ))⁻¹ * ((X : ℝ) / 2 ^ e) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self X (2 ^ e)
      _ = (1 / 2 : ℝ) ^ e := by rw [div_pow, one_pow]; field_simp
  have hT := tendsto_tsum_of_dominated_convergence
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hlayer
    (Eventually.of_forall (hbound ·))
  rw [tsum_zero] at hT
  exact hT.congr' (Eventually.of_forall fun X => by simp only [hconv]; exact (hsum X).symm)

/-- **Lemma 6.5 [`lem:sampling`] at a fixed frequency, odd sources** (proof of Theorem 6.13, the
`G = U` case: "keep odd sources throughout"): for a set of odd integers, only the layer `e = 0`
contributes. -/
theorem uniform_of_odd_dyadic_fixed_odd {A : Set ℕ} {q : ℕ → ℝ} (hA : ∀ n ∈ A, Odd n) (s : ℝ)
    (hodd : Tendsto (fun Y : ℝ => phi0 A q Y s) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => (X : ℂ)⁻¹ *
      ∑ n ∈ Icc 1 X, A.indicator (fun n => cexp (((s * q n : ℝ) : ℂ) * I)) n) atTop (𝓝 0) := by
  classical
  have hinner := dyadic_tannery (L := atTop) (Z := fun X : ℕ => X)
    (f := fun X u => if Odd u then ph A q s (0 * Real.log (u : ℝ)) u else 0)
    (fun X u => by split_ifs <;> simp [norm_ph_le])
    (ℓ := 0) (fun k => by
      simpa using block_limit_fixed (e0 := 0) s hodd 0 k ⟨0, fun u _ => by simp⟩)
  refine hinner.congr' (Eventually.of_forall fun X => ?_)
  congr 1
  refine sum_congr rfl fun n _ => ?_
  by_cases hn : Odd n
  · rw [ite_eq_left hn, ph_zero_mul]
  · rw [ite_eq_right hn, Set.indicator_of_notMem (fun h => hn (hA n h))]

end Sampling

/-! ## Decay of the phase average at a nonzero frequency `2πr/Q₀` -/

/-- `u^{-a} log u ≤ (2/a) v^{-a/2}` for `0 < v ≤ u`: the kernel bound of Proposition 4.5 is
dominated, on `u ≥ v`, by a quantity that tends to `0` as `v → ∞`. -/
lemma rpow_neg_mul_log_le {a u v : ℝ} (ha : 0 < a) (hv : 0 < v) (hvu : v ≤ u) :
    u ^ (-a) * Real.log u ≤ 2 / a * v ^ (-(a / 2)) := by
  have hu : 0 < u := hv.trans_le hvu
  have hlog : Real.log u ≤ u ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hu.le (by positivity)
  have h1 : u ^ (-a) * u ^ (a / 2) = u ^ (-(a / 2)) := by
    rw [← Real.rpow_add hu]; ring_nf
  have h2 : u ^ (-(a / 2)) ≤ v ^ (-(a / 2)) :=
    Real.rpow_le_rpow_of_nonpos hv hvu (by linarith)
  calc u ^ (-a) * Real.log u ≤ u ^ (-a) * (u ^ (a / 2) / (a / 2)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 / a * u ^ (-(a / 2)) := by rw [← h1]; field_simp
    _ ≤ 2 / a * v ^ (-(a / 2)) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `r/Q₀` in lowest terms: for `0 < r < Q₀`, `2πr/Q₀ = 2πr'/Q'` with `gcd(r', Q') = 1` and
`Q' ≥ 2`. -/
lemma exists_lowest_terms {r Q₀ : ℕ} (hr : 0 < r) (hrQ : r < Q₀) :
    ∃ r' Q' : ℕ, 2 ≤ Q' ∧ Int.gcd (r' : ℤ) Q' = 1 ∧
      (2 * π * r / Q₀ : ℝ) = 2 * π * ((r' : ℤ) : ℝ) / Q' := by
  have hg0 : 0 < Nat.gcd r Q₀ := Nat.gcd_pos_of_pos_left _ hr
  -- `r = r'g`, `Q₀ = Q'g` with `g = gcd(r, Q₀)` and `gcd(r', Q') = 1`
  obtain ⟨g, r', Q', hg, rfl, rfl, hcop⟩ : ∃ g r' Q' : ℕ, 0 < g ∧ r = r' * g ∧ Q₀ = Q' * g ∧
      Nat.Coprime r' Q' :=
    ⟨_, _, _, hg0, (Nat.div_mul_cancel (Nat.gcd_dvd_left r Q₀)).symm,
      (Nat.div_mul_cancel (Nat.gcd_dvd_right r Q₀)).symm, Nat.coprime_div_gcd_div_gcd hg0⟩
  have hr' : 0 < r' := Nat.pos_of_mul_pos_right hr
  have hrQ' : r' < Q' := Nat.lt_of_mul_lt_mul_right hrQ
  refine ⟨r', Q', by omega, by rw [Int.gcd_natCast_natCast]; exact hcop, ?_⟩
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hQR : (Q' : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q' ≠ 0)
  push_cast
  field_simp

/-- **The odd dyadic phase average decays at a nonzero frequency** (proof of Theorem 6.13): for a
set and clock with the transport property (6.2, `eq:transport`) and a coprime integer reward,
`E[1_A(N_Y) e^{isq(N_Y)}] → 0` at `s = 2πr/Q₀`, `0 < r < Q₀`, by `phi0_le_of_kernel` and
Proposition 4.5 [`prop:fixedfreq`] on `u ≥ c₀ log Y`. -/
theorem phi0_tendsto_zero (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (ρ η : ℕ) (hco : Nat.Coprime ρ η) {A : Set ℕ} {q : ℕ → ℝ} {x₀ : ℝ}
    (htr : Transport A q ρ η x₀) {Q₀ r : ℕ} (hr : 0 < r) (hrQ : r < Q₀) :
    Tendsto (fun Y : ℝ => phi0 A q Y (2 * π * r / Q₀)) atTop (𝓝 0) := by
  obtain ⟨r', Q', hQ', hgcd, hs⟩ := exists_lowest_terms hr hrQ
  obtain ⟨C, hC⟩ := fixedfreq hθ ρ η hco Q' hQ'
  obtain ⟨C₁, C₂, x₁, c₀, hc₀, hK⟩ := phi0_le_of_kernel hTM hTP ρ η
  have ha : 0 < 1 / (2 * (ϰ + 1)) := by have := hθ.2.1; positivity
  set a : ℝ := 1 / (2 * (ϰ + 1)) with ha_def
  have hlog : Tendsto (fun Y : ℝ => c₀ * Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hc₀
  -- the bound `B(Y) = |C| (2/a) (c₀ log Y)^{-a/2}` on the kernel, and `C₁ B(Y) + C₂/log Y → 0`
  have hBlim : Tendsto (fun Y : ℝ =>
      C₁ * (|C| * (2 / a * (c₀ * Real.log Y) ^ (-(a / 2)))) + C₂ / Real.log Y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Y : ℝ => (c₀ * Real.log Y) ^ (-(a / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity)).comp hlog
    have h2 : Tendsto (fun Y : ℝ => C₂ / Real.log Y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using (((h1.const_mul (2 / a)).const_mul |C|).const_mul C₁).add h2
  refine squeeze_zero_norm' ?_ hBlim
  filter_upwards [eventually_ge_atTop ((max x₁ x₀) ^ alpha),
    hlog.eventually (eventually_ge_atTop 2)] with Y hY hY2
  refine hK A q x₀ htr _ Y hY _ fun u hu => ?_
  have hu2 : 2 ≤ u := hY2.trans hu
  have hpos : 0 ≤ u ^ (-a) * Real.log u :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith))
  rw [hs]
  calc ‖renewalR ρ η (2 * π * ((r' : ℤ) : ℝ) / Q') u‖ ≤ C * u ^ (-a) * Real.log u :=
        hC r' hgcd u hu2
    _ = C * (u ^ (-a) * Real.log u) := by ring
    _ ≤ |C| * (u ^ (-a) * Real.log u) := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * (2 / a * (c₀ * Real.log Y) ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left (rpow_neg_mul_log_le ha (by linarith) hu) (abs_nonneg C)

/-! ## Finite Fourier inversion on `ZMod Q₀` -/

/-- `∑_{r<Q₀} e^{2πirm/Q₀} = Q₀·1{Q₀ ∣ m}`, by `geom_sum_eq` for a nontrivial `Q₀`-th root of
unity. -/
lemma sum_range_cexp_int {Q₀ : ℕ} (hQ : 1 ≤ Q₀) (m : ℤ) :
    ∑ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * m : ℝ) : ℂ) * I) =
      if (Q₀ : ℤ) ∣ m then (Q₀ : ℂ) else 0 := by
  have hQ0 : (Q₀ : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q₀ ≠ 0)
  have hQ0c : (Q₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q₀ ≠ 0)
  set ζ : ℂ := cexp (((2 * π * m / Q₀ : ℝ) : ℂ) * I) with hζ
  have hpow : ∀ r : ℕ, cexp (((2 * π * r / Q₀ * m : ℝ) : ℂ) * I) = ζ ^ r := by
    intro r
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [hpow]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have h1 : ζ = 1 := by
      rw [hζ]
      have : (((2 * π * ((Q₀ * k : ℤ) : ℝ) / Q₀ : ℝ)) : ℂ) * I = (k : ℂ) * (2 * π * I) := by
        push_cast
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [h1]
  · have hne : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hrhs : (n : ℂ) * (2 * π * I) = ((n * (2 * π) : ℝ) : ℂ) * I := by push_cast; ring
      rw [hrhs] at hn
      have h2 : (2 * π * m / Q₀ : ℝ) = n * (2 * π) :=
        Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hn)
      have h3 : 2 * π * (m : ℝ) = n * (2 * π) * Q₀ := (div_eq_iff hQ0).mp h2
      have hm : (m : ℝ) = (n * Q₀ : ℤ) := by
        push_cast
        refine mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) ?_
        linear_combination h3
      exact hdvd ⟨n, by rw [mul_comm]; exact_mod_cast hm⟩
    have hQ : ζ ^ Q₀ = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (Q₀ : ℂ) * (((2 * π * m / Q₀ : ℝ) : ℂ) * I) = (m : ℂ) * (2 * π * I) := by
        push_cast
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hne, hQ, sub_self, zero_div]

/-- **Fourier inversion at one point:** `Q₀⁻¹ ∑_{r<Q₀} e^{2πirr₀/Q₀}·1_A(n) e^{-2πirτ(n)/Q₀}` is
the indicator of `{n ∈ A : τ(n) ≡ r₀ (mod Q₀)}`. -/
lemma fourier_indicator {Q₀ : ℕ} (hQ : 1 ≤ Q₀) (A : Set ℕ) (τ : ℕ → ℕ) (r₀ : ZMod Q₀) (n : ℕ) :
    (Q₀ : ℂ)⁻¹ * ∑ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) *
      A.indicator (fun n => cexp (((2 * π * r / Q₀ * -(τ n : ℝ) : ℝ) : ℂ) * I)) n =
    {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀}.indicator (fun _ => (1 : ℂ)) n := by
  have : NeZero Q₀ := ⟨by omega⟩
  have hQ0 : (Q₀ : ℂ) ≠ 0 := by exact_mod_cast (by omega : Q₀ ≠ 0)
  by_cases hn : n ∈ A
  · simp only [Set.indicator_of_mem hn]
    have hcomb : ∀ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) *
        cexp (((2 * π * r / Q₀ * -(τ n : ℝ) : ℝ) : ℂ) * I) =
        cexp (((2 * π * r / Q₀ * ((r₀.val : ℤ) - τ n : ℤ) : ℝ) : ℂ) * I) := by
      intro r _
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [sum_congr rfl hcomb, sum_range_cexp_int hQ]
    have hiff : (Q₀ : ℤ) ∣ ((r₀.val : ℤ) - τ n) ↔ ((τ n : ℕ) : ZMod Q₀) = r₀ := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, sub_eq_zero, eq_comm]
    by_cases hc : ((τ n : ℕ) : ZMod Q₀) = r₀
    · rw [ite_eq_left (hiff.mpr hc), Set.indicator_of_mem (show n ∈ {n | n ∈ A ∧
        ((τ n : ℕ) : ZMod Q₀) = r₀} from ⟨hn, hc⟩), inv_mul_cancel₀ hQ0]
    · rw [ite_eq_right (fun h => hc (hiff.mp h)), Set.indicator_of_notMem (show n ∉ {n | n ∈ A ∧
        ((τ n : ℕ) : ZMod Q₀) = r₀} from fun h => hc h.2), mul_zero]
  · rw [Set.indicator_of_notMem (show n ∉ {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀} from
      fun h => hn h.1)]
    simp [Set.indicator_of_notMem hn]

/-- `∑_{n ≤ X} 1_S(n) = #(S ∩ [1, X])`. -/
lemma sum_indicator_one_eq_card (S : Set ℕ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, S.indicator (fun _ => (1 : ℂ)) n = ((window S X).card : ℂ) := by
  classical
  unfold window
  rw [Finset.card_filter]
  push_cast
  refine sum_congr rfl fun n _ => ?_
  simp [Set.indicator_apply]

/-- **Finite Fourier inversion on `ZMod Q₀`** (proof of Theorem 6.13): if `A` has density `p` and
the phase averages of the clock `-τ` at the nonzero frequencies `2πr/Q₀`, `0 < r < Q₀`, tend to
`0`, then every residue class of `τ` in `A` has density `p/Q₀`. -/
theorem hasDensity_mod_of_phases {A : Set ℕ} {τ : ℕ → ℕ} {Q₀ : ℕ} (hQ : 1 ≤ Q₀) {p : ℝ}
    (hA : HasDensity A p)
    (hph : ∀ r : ℕ, 0 < r → r < Q₀ → Tendsto (fun X : ℕ => (X : ℂ)⁻¹ *
      ∑ n ∈ Icc 1 X, A.indicator (fun n => cexp (((2 * π * r / Q₀ * -(τ n : ℝ) : ℝ) : ℂ) * I)) n)
      atTop (𝓝 0))
    (r₀ : ZMod Q₀) :
    HasDensity {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀} (p / Q₀) := by
  classical
  -- the phase average at frequency `2πr/Q₀`
  set avg : ℕ → ℕ → ℂ := fun r X => (X : ℂ)⁻¹ *
    ∑ n ∈ Icc 1 X, A.indicator (fun n => cexp (((2 * π * r / Q₀ * -(τ n : ℝ) : ℝ) : ℂ) * I)) n
    with havg
  -- `r = 0` gives the density of `A`, the other frequencies give `0`
  have hlim : ∀ r ∈ range Q₀,
      Tendsto (fun X => cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) * avg r X) atTop
        (𝓝 (cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) * (if r = 0 then (p : ℂ) else 0))) := by
    intro r hr
    refine tendsto_const_nhds.mul ?_
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      rw [ite_eq_left rfl]
      have hc := (Complex.continuous_ofReal.tendsto p).comp hA
      refine hc.congr' (Eventually.of_forall fun X => ?_)
      simp only [Function.comp_apply, havg, Nat.cast_zero, mul_zero, zero_div, zero_mul,
        Complex.ofReal_zero, Complex.exp_zero]
      rw [sum_indicator_one_eq_card]
      push_cast
      ring
    · rw [ite_eq_right hpos.ne']
      exact hph r hpos (mem_range.mp hr)
  have hsum := tendsto_finsetSum (range Q₀) hlim
  have hval : ∑ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) *
      (if r = 0 then (p : ℂ) else 0) = p := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  rw [hval] at hsum
  have hfin := hsum.const_mul ((Q₀ : ℂ)⁻¹)
  -- the counting identity
  have hid : ∀ X : ℕ, (Q₀ : ℂ)⁻¹ *
      ∑ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) * avg r X =
      ((((window {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀} X).card : ℝ) / X : ℝ) : ℂ) := by
    intro X
    calc (Q₀ : ℂ)⁻¹ * ∑ r ∈ range Q₀, cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) * avg r X
        = (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ((Q₀ : ℂ)⁻¹ * ∑ r ∈ range Q₀,
            cexp (((2 * π * r / Q₀ * r₀.val : ℝ) : ℂ) * I) *
              A.indicator (fun n => cexp (((2 * π * r / Q₀ * -(τ n : ℝ) : ℝ) : ℂ) * I)) n) := by
          simp only [havg, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun n _ => sum_congr rfl fun r _ => ?_
          ring
      _ = (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X,
            {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀}.indicator (fun _ => (1 : ℂ)) n := by
          congr 1
          exact sum_congr rfl fun n _ => fourier_indicator hQ A τ r₀ n
      _ = _ := by
          rw [sum_indicator_one_eq_card]
          push_cast
          ring
  have hC := hfin.congr' (Eventually.of_forall hid)
  have hval' : (Q₀ : ℂ)⁻¹ * (p : ℂ) = ((p / Q₀ : ℝ) : ℂ) := by push_cast; ring
  rw [hval'] at hC
  have hre := (Complex.continuous_re.tendsto _).comp hC
  rw [Complex.ofReal_re] at hre
  exact hre.congr fun X => by simp only [Function.comp_apply, Complex.ofReal_re]

/-! ## Theorem 6.13 -/

-- `3 ∤ b` is part of the audited hypothesis "b as in Theorem 1.1"; the proof does not use it.
set_option linter.unusedVariables false in
/-- **Theorem 6.13 [`thm:modq`] (equidistribution modulo `Q₀`).** For `b` as in Theorem 1.1
(`0 < b`, `3 ∤ b`), `Q₀ ≥ 2` and every residue `r₀`: with `p = dens P_G(b)` (which exists by
Theorem 1.1(i)), `dens {n ∈ P_G(b) : τ_{G,b}(n) ≡ r₀ (mod Q₀)} = p/Q₀`, for `G = T`, `G = F`, and
for `G = U` with `b` odd and odd sources (`P_U(b)` is odd; ordinary natural densities, as in the
proof). -/
theorem modq (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) (Q₀ : ℕ) (hQ : 2 ≤ Q₀) :
    (∀ p : ℝ, HasDensity (Pred T b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ Pred T b ∧ ((hit T b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) ∧
    (∀ p : ℝ, HasDensity (Pred F b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ Pred F b ∧ ((hit F b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) ∧
    (Odd b → ∀ p : ℝ, HasDensity (PredU b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ PredU b ∧ ((hit U b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) := by
  have hQ1 : 1 ≤ Q₀ := by omega
  -- one clock: transport, coprime integer reward and fixed-frequency sampling give the residues
  have key : ∀ (ρ η : ℕ), Nat.Coprime ρ η → ∀ (A : Set ℕ) (τ : ℕ → ℕ) (x₀ : ℝ),
      Transport A (fun n => -(τ n : ℝ)) ρ η x₀ →
      (∀ s : ℝ, Tendsto (fun Y : ℝ => phi0 A (fun n => -(τ n : ℝ)) Y s) atTop (𝓝 0) →
        Tendsto (fun X : ℕ => (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X,
          A.indicator (fun n => cexp (((s * -(τ n : ℝ) : ℝ) : ℂ) * I)) n) atTop (𝓝 0)) →
      ∀ p : ℝ, HasDensity A p → ∀ r₀ : ZMod Q₀,
        HasDensity {n | n ∈ A ∧ ((τ n : ℕ) : ZMod Q₀) = r₀} (p / Q₀) := by
    intro ρ η hco A τ x₀ htr hsamp p hA r₀
    exact hasDensity_mod_of_phases hQ1 hA (fun r hr hrQ =>
      hsamp _ (phi0_tendsto_zero hTM hTP hθ ρ η hco htr hr hrQ)) r₀
  refine ⟨fun p hp r₀ => key 1 1 (by norm_num) (Pred T b) (hit T b) (b + 1)
      (by simpa using transport_T b)
      (fun s h => uniform_of_odd_dyadic_fixed (doubling_T b hb) s h) p hp r₀,
    fun p hp r₀ => key 1 0 (by norm_num) (Pred F b) (hit F b) (b + 1)
      (by simpa using transport_F b)
      (fun s h => uniform_of_odd_dyadic_fixed (doubling_F b hb) s h) p hp r₀,
    fun _ p hp r₀ => key 0 1 (by norm_num) (PredU b) (hit U b) (b + 1)
      (by simpa using transport_U b)
      (fun s h => uniform_of_odd_dyadic_fixed_odd (fun n hn => hn.2.1) s h) p hp r₀⟩

end CollatzCLT
