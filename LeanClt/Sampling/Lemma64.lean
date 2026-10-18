import LeanClt.Sampling.Basic

/-!
# Lemma 6.5 [`lem:sampling`]: from odd dyadic sampling to uniform sampling on `[1, X]`

Hypotheses:
* the sequential conclusion of Proposition 6.2 for the odd dyadic characteristic function
  `oddCF A q κ`: along any scales `Y_X → ∞` and frequencies `s_X` with
  `s_X √(log Y_X) → τ`, `Φ_{Y_X}(s_X) → e^{-D τ²} p`;
* doubling compatibility (as in Lemma 6.5 [`lem:sampling`]): for all large `n`, `2n ∈ A ↔ n ∈ A`, and
  `q(2n) = q(n) - e₀` on `A`.

Conclusion: the `[1, X]` clause of Lemma 6.5(ii) [`lem:sampling`], in sequential form and with the
centring `κ log n` at the sampled point in place of `κ log X` (a deviation from the printed
lemma):
`X⁻¹ ∑_{n ≤ X} 1_A(n) e^{i s_X (q(n) + κ log n)} → e^{-D τ²} p` whenever `s_X √(log X) → τ`.
No positivity is assumed. Lemma 6.5(iii), the replacement of `κ log X` by `κ log N_X` under
sampling conditioned on `A` when `p(A) > 0`, is `cltOn_of_logX` (`Exceptional/Laws.lean`).

The proof splits `n = 2^e u` (`u` odd) and then splits `u` into dyadic blocks
`(⌊Z/2^{k+1}⌋, ⌊Z/2^k⌋]`. On a block at scale `W`:
* doubling turns `2^e u` into `u` at the cost of a phase `e^{i s e (κ log 2 - e₀)} → 1`;
* the half-open block differs from `[W, 2W]` in at most two points;
* recentring `κ log u` at `κ log W` costs at most `|s| |κ| log 2` per point.
Two applications of Tannery's theorem (blocks `k`, then valuations `e`) replace the
truncations `J₀ → ∞`, `E₀ → ∞` of the paper.
-/

open Real Filter Topology Finset Complex

namespace CollatzCLT

variable {A : Set ℕ} {q : ℕ → ℝ} {κ e0 : ℝ}

/-- The doubling hypothesis of Lemma 6.5 [`lem:sampling`]. -/
def DoublingCompatible (A : Set ℕ) (q : ℕ → ℝ) (e0 : ℝ) : Prop :=
  ∃ n0 : ℕ, ∀ n ≥ n0, (2 * n ∈ A ↔ n ∈ A) ∧ (n ∈ A → q (2 * n) = q n - e0)

/-- Iterated doubling. -/
lemma DoublingCompatible.iterate (h : DoublingCompatible A q e0) :
    ∃ n0 : ℕ, ∀ e u : ℕ, n0 ≤ u → (2 ^ e * u ∈ A ↔ u ∈ A) ∧ (u ∈ A → q (2 ^ e * u) = q u - e * e0) := by
  obtain ⟨n0, hn0⟩ := h
  refine ⟨n0, fun e u hu => ?_⟩
  induction e with
  | zero => simp
  | succ e ih =>
    have hge : n0 ≤ 2 ^ e * u := le_trans hu (Nat.le_mul_of_pos_left u (by positivity))
    have h2 := hn0 _ hge
    have heq : 2 ^ (e + 1) * u = 2 * (2 ^ e * u) := by ring
    rw [heq]
    refine ⟨h2.1.trans ih.1, fun hA => ?_⟩
    rw [h2.2 (ih.1.mpr hA), ih.2 hA]
    push_cast; ring

/-- **Phase factoring.** For `u ≥ n₀` (`u > 0`), the phase at `2^e u` (centred at
`κ log(2^e u)`) is the phase at `u` (centred at `κ log u`) times `e^{i s e (κ log 2 - e₀)}`. -/
lemma ph_two_pow_mul {n0 : ℕ} (e : ℕ)
    (hdbl : ∀ u : ℕ, n0 ≤ u → (2 ^ e * u ∈ A ↔ u ∈ A) ∧ (u ∈ A → q (2 ^ e * u) = q u - e * e0))
    (s : ℝ) {u : ℕ} (hu : n0 ≤ u) (hu0 : 0 < u) :
    ph A q s (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) =
      cexp (((s * (e * (κ * Real.log 2 - e0)) : ℝ) : ℂ) * I) * ph A q s (κ * Real.log u) u := by
  obtain ⟨hmem, hq⟩ := hdbl u hu
  unfold ph
  by_cases hA : u ∈ A
  · rw [Set.indicator_of_mem (hmem.mpr hA), Set.indicator_of_mem hA, ← Complex.exp_add]
    congr 1
    have hlog : Real.log ((2 ^ e * u : ℕ) : ℝ) = e * Real.log 2 + Real.log u := by
      push_cast
      rw [Real.log_mul (by positivity) (by exact_mod_cast hu0.ne'), Real.log_pow]
    rw [hq hA, hlog]
    push_cast; ring
  · rw [Set.indicator_of_notMem (fun h => hA (hmem.mp h)), Set.indicator_of_notMem hA, mul_zero]

/-- The half-open odd block `(W, V]`, `2W ≤ V ≤ 2W+1`, differs from `[W, 2W]` in at most two
points. -/
lemma norm_sum_block_sub_oddClosed_le {W V : ℕ} (hV1 : 2 * W ≤ V) (hV2 : V ≤ 2 * W + 1)
    (f : ℕ → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖∑ u ∈ (Ioc W V).filter Odd, f u - ∑ u ∈ oddClosed (W : ℝ), f u‖ ≤ 2 := by
  rw [oddClosed_natCast, ← sum_sdiff_sub_sum_sdiff]
  have h1 : ((Ioc W V).filter Odd \ (Icc W (2 * W)).filter Odd) ⊆ {2 * W + 1} := by
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, not_and] at hu
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hu.2 ⟨by omega, by omega⟩ hu.1.2
  have h2 : ((Icc W (2 * W)).filter Odd \ (Ioc W V).filter Odd) ⊆ {W} := by
    intro u hu
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, not_and] at hu
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hu.2 ⟨by omega, by omega⟩ hu.1.2
  have hb : ∀ S : Finset ℕ, S ⊆ {W} ∨ S ⊆ {2 * W + 1} → ‖∑ u ∈ S, f u‖ ≤ 1 := by
    intro S hS
    have hcard : S.card ≤ 1 := by
      rcases hS with hS | hS
      · exact (card_le_card hS).trans (by simp)
      · exact (card_le_card hS).trans (by simp)
    calc ‖∑ u ∈ S, f u‖ ≤ ∑ u ∈ S, ‖f u‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ S, (1 : ℝ) := sum_le_sum fun u _ => hf u
      _ = S.card := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  calc ‖∑ u ∈ (Ioc W V).filter Odd \ (Icc W (2 * W)).filter Odd, f u
        - ∑ u ∈ (Icc W (2 * W)).filter Odd \ (Ioc W V).filter Odd, f u‖
      ≤ ‖∑ u ∈ (Ioc W V).filter Odd \ (Icc W (2 * W)).filter Odd, f u‖
        + ‖∑ u ∈ (Icc W (2 * W)).filter Odd \ (Ioc W V).filter Odd, f u‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (hb _ (Or.inr h1)) (hb _ (Or.inl h2))
    _ = 2 := by norm_num

/-- Recentring `κ log u` at `κ log W` on `[W, 2W]` costs at most `|s| |κ| log 2` per point. -/
lemma norm_sum_recentre_le {W : ℕ} (hW : 1 ≤ W) (s : ℝ) :
    ‖∑ u ∈ oddClosed (W : ℝ), (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u)‖
      ≤ (oddClosed (W : ℝ)).card * (|s| * (|κ| * Real.log 2)) := by
  calc ‖∑ u ∈ oddClosed (W : ℝ), (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u)‖
      ≤ ∑ u ∈ oddClosed (W : ℝ), ‖ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ u ∈ oddClosed (W : ℝ), |s| * (|κ| * Real.log 2) := by
        apply sum_le_sum
        intro u hu
        rw [oddClosed_natCast, Finset.mem_filter, Finset.mem_Icc] at hu
        have hW' : (0 : ℝ) < W := by exact_mod_cast hW
        have hu1 : (W : ℝ) ≤ u := by exact_mod_cast hu.1.1
        have hu2 : (u : ℝ) ≤ 2 * W := by exact_mod_cast hu.1.2
        have hlog : |Real.log u - Real.log W| ≤ Real.log 2 := by
          rw [← Real.log_div (by linarith) hW'.ne', abs_of_nonneg
            (Real.log_nonneg ((one_le_div hW').mpr hu1))]
          exact Real.log_le_log (div_pos (by linarith) hW') ((div_le_iff₀ hW').mpr (by linarith))
        refine (norm_ph_sub_le A q s _ _ u).trans ?_
        rw [← mul_sub, abs_mul]
        gcongr
    _ = (oddClosed (W : ℝ)).card * (|s| * (|κ| * Real.log 2)) := by simp

/-- The block endpoints: `W = ⌊Z/2^{k+1}⌋` and `V = ⌊Z/2^k⌋` satisfy `2W ≤ V ≤ 2W + 1`. -/
lemma block_endpoints (Z k : ℕ) :
    2 * (Z / 2 ^ (k + 1)) ≤ Z / 2 ^ k ∧ Z / 2 ^ k ≤ 2 * (Z / 2 ^ (k + 1)) + 1 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- The sequential conclusion of Proposition 6.2 for `oddCF A q κ`, along ℕ-indexed scales. -/
def SeqLimit (A : Set ℕ) (q : ℕ → ℝ) (κ D : ℝ) (p : ℂ) : Prop :=
  ∀ (Y sY : ℕ → ℝ) (τ : ℝ), Tendsto Y atTop atTop →
    Tendsto (fun X => sY X * √(Real.log (Y X))) atTop (𝓝 τ) →
    Tendsto (fun X => oddCF A q κ (Y X) (sY X)) atTop (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p))

/-- `s_X √(log X) → τ` forces `s_X → 0`. -/
lemma tendsto_zero_of_mul_sqrt_log {sX : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ)) : Tendsto sX atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun X : ℕ => √(Real.log X)) atTop atTop :=
    (tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  refine (hτ.div_atTop hsqrt).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with X hX
  have := Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hX : (1 : ℝ) < X))
  field_simp

/-- Error from the two endpoints of the half-open block `(W, V]`. -/
noncomputable def err1 (A : Set ℕ) (q : ℕ → ℝ) (κ s : ℝ) (W V : ℕ) : ℂ :=
  ∑ u ∈ (Ioc W V).filter Odd, ph A q s (κ * Real.log u) u -
    ∑ u ∈ oddClosed (W : ℝ), ph A q s (κ * Real.log u) u

/-- Error from recentring `κ log u` at `κ log W`. -/
noncomputable def err2 (A : Set ℕ) (q : ℕ → ℝ) (κ s : ℝ) (W : ℕ) : ℂ :=
  ∑ u ∈ oddClosed (W : ℝ), (ph A q s (κ * Real.log u) u - ph A q s (κ * Real.log W) u)

/-- The block sum is `#oddClosed(W) · Φ_W(s)` plus the two errors. -/
lemma block_sum_eq (A : Set ℕ) (q : ℕ → ℝ) (κ s : ℝ) (W V : ℕ)
    (hc : ((oddClosed (W : ℝ)).card : ℂ) ≠ 0) :
    ∑ u ∈ (Ioc W V).filter Odd, ph A q s (κ * Real.log u) u =
      err1 A q κ s W V + err2 A q κ s W + ((oddClosed (W : ℝ)).card : ℂ) * oddCF A q κ W s := by
  unfold err1 err2 oddCF
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sum_sub_distrib]
  ring

/-- **Block limit.** For fixed `e` and `k` (with doubling compatibility at that `e`; at `e = 0`
this is automatic), the sum over the `k`-th dyadic block of
`[1, ⌊X/2^e⌋]` of the odd-part phases `1_{u odd} ph(2^e u)`, divided by `⌊X/2^e⌋`, tends to
`ℓ / 2 / 2^{k+1}`, where `ℓ = e^{-D τ²} p`. -/
theorem block_limit {D : ℝ} {p : ℂ} (hseq : SeqLimit A q κ D p) (e k : ℕ)
    (hdble : ∃ n0 : ℕ, ∀ u : ℕ, n0 ≤ u →
      (2 ^ e * u ∈ A ↔ u ∈ A) ∧ (u ∈ A → q (2 ^ e * u) = q u - e * e0))
    {sX : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ)) :
    Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℂ)⁻¹ *
      ∑ u ∈ Ioc ((X / 2 ^ e) / 2 ^ (k + 1)) ((X / 2 ^ e) / 2 ^ k),
        (if Odd u then ph A q (sX X) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) else 0))
      atTop (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p / 2 / 2 ^ (k + 1))) := by
  classical
  obtain ⟨n0, hn0⟩ := hdble
  have hmpos : 0 < 2 ^ (e + k + 1) := by positivity
  have he0 : 0 < 2 ^ e := by positivity
  have hZW : ∀ X : ℕ, X / 2 ^ e / 2 ^ (k + 1) = X / 2 ^ (e + k + 1) := by
    intro X; rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
  have hs0 := tendsto_zero_of_mul_sqrt_log hτ
  -- (a) the odd dyadic characteristic function at scale `W = ⌊X/2^{e+k+1}⌋`
  have hcf : Tendsto (fun X : ℕ => oddCF A q κ ((X / 2 ^ (e + k + 1) : ℕ) : ℝ) (sX X)) atTop
      (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p)) :=
    hseq _ _ τ (tendsto_natCast_atTop_atTop.comp (tendsto_natDiv_atTop hmpos))
      (tendsto_mul_sqrt_log_natDiv hmpos hτ)
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
      calc (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / X) / 2 = (((X / 2 ^ (e + k + 1) : ℕ) : ℝ) / 2) / X := by
            ring
        _ ≤ _ := div_le_div_of_nonneg_right hb hXpos.le
    · filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1))] with X hX
      have hW1 : 1 ≤ X / 2 ^ (e + k + 1) := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa using hX)
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le hmpos hX)
      have hb := (card_oddClosed_bounds hW1).2
      calc _ ≤ ((((X / 2 ^ (e + k + 1) : ℕ) : ℝ)) / 2 + 1) / X := div_le_div_of_nonneg_right hb hXpos.le
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
  -- (c) the phase factor tends to `1`
  have hφ : Tendsto (fun X => cexp (((sX X * (e * (κ * Real.log 2 - e0)) : ℝ) : ℂ) * I)) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun X => sX X * (e * (κ * Real.log 2 - e0))) atTop (𝓝 0) := by
      simpa using hs0.mul_const (e * (κ * Real.log 2 - e0))
    have hc : Continuous (fun x : ℝ => cexp ((x : ℂ) * I)) := by fun_prop
    have := (hc.tendsto 0).comp h1
    have h0 : cexp (((0 : ℝ) : ℂ) * I) = 1 := by simp
    rw [h0] at this
    exact this
  -- (d) the two error terms, normalised by `Z`
  have hZtop : Tendsto (fun X : ℕ => ((X / 2 ^ e : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_natDiv_atTop he0)
  have hR1 : Tendsto (fun X : ℕ => (((X / 2 ^ e : ℕ) : ℂ))⁻¹ *
      err1 A q κ (sX X) (X / 2 ^ (e + k + 1)) (X / 2 ^ e / 2 ^ k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun X => 2 / ((X / 2 ^ e : ℕ) : ℝ))
    · refine Eventually.of_forall fun X => ?_
      have h1 : 2 * (X / 2 ^ (e + k + 1)) ≤ X / 2 ^ e / 2 ^ k := by
        rw [← hZW]; exact (block_endpoints (X / 2 ^ e) k).1
      have h2 : X / 2 ^ e / 2 ^ k ≤ 2 * (X / 2 ^ (e + k + 1)) + 1 := by
        rw [← hZW]; exact (block_endpoints (X / 2 ^ e) k).2
      have hb := norm_sum_block_sub_oddClosed_le h1 h2
        (fun u => ph A q (sX X) (κ * Real.log u) u) (fun u => norm_ph_le _ _ _ _ _)
      rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
      gcongr
      exact hb
    · simpa using (tendsto_const_nhds (x := (2 : ℝ))).div_atTop hZtop
  have hR2 : Tendsto (fun X : ℕ => (((X / 2 ^ e : ℕ) : ℂ))⁻¹ *
      err2 A q κ (sX X) (X / 2 ^ (e + k + 1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun X =>
      (((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℝ) / ((X / 2 ^ e : ℕ) : ℝ)) *
        (|sX X| * (|κ| * Real.log 2)))
    · filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1))] with X hX
      have hW1 : 1 ≤ X / 2 ^ (e + k + 1) := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa using hX)
      have hb := norm_sum_recentre_le (A := A) (q := q) (κ := κ) hW1 (sX X)
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc _ ≤ (((X / 2 ^ e : ℕ) : ℝ))⁻¹ * (((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℝ) *
            (|sX X| * (|κ| * Real.log 2))) := by gcongr; exact hb
        _ = _ := by ring
    · have := hcZ.mul ((hs0.abs).mul_const (|κ| * Real.log 2))
      simpa using this
  -- (e) assemble
  have hlim := hφ.mul ((((Complex.continuous_ofReal.tendsto _).comp hcZ).mul hcf).add hR1
    |>.add hR2)
  have hval : (1 : ℂ) * (((1 / 2 ^ (k + 2) : ℝ) : ℂ) * ((Real.exp (-(D * τ ^ 2)) : ℂ) * p) + 0 + 0)
      = (Real.exp (-(D * τ ^ 2)) : ℂ) * p / 2 / 2 ^ (k + 1) := by
    push_cast; rw [pow_succ, pow_succ]; field_simp; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 ^ (e + k + 1) * (n0 + 1))] with X hX
  have hWn0 : n0 + 1 ≤ X / 2 ^ (e + k + 1) :=
    (Nat.le_div_iff_mul_le hmpos).mpr (by linarith [hX])
  have hcpos : ((oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card : ℂ) ≠ 0 := by
    have hb := (card_oddClosed_bounds (W := X / 2 ^ (e + k + 1)) (by omega)).1
    have hW' : (0 : ℝ) < ((X / 2 ^ (e + k + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < X / 2 ^ (e + k + 1))
    have hne : (oddClosed ((X / 2 ^ (e + k + 1) : ℕ) : ℝ)).card ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at hb
      linarith
    exact_mod_cast hne
  -- rewrite the block sum
  have hfac : ∀ u ∈ (Ioc (X / 2 ^ (e + k + 1)) (X / 2 ^ e / 2 ^ k)).filter Odd,
      ph A q (sX X) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) =
      cexp (((sX X * (e * (κ * Real.log 2 - e0)) : ℝ) : ℂ) * I) *
        ph A q (sX X) (κ * Real.log u) u := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Ioc] at hu
    have h1 : X / 2 ^ (e + k + 1) < u := hu.1.1
    exact ph_two_pow_mul e hn0 (sX X) (by omega) (by omega)
  rw [hZW, ← sum_filter, sum_congr rfl hfac, ← mul_sum,
    block_sum_eq A q κ (sX X) _ _ hcpos]
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **Lemma 6.5 [`lem:sampling`] (uniform sampling on `[1, X]`).** Under the sequential conclusion of
Proposition 6.2 for odd dyadic sampling and doubling compatibility, for every `s_X` with
`s_X √(log X) → τ`,
`X⁻¹ ∑_{n ≤ X} 1_A(n) e^{i s_X (q(n) + κ log n)} → e^{-D τ²} p`. -/
theorem uniform_limit {D : ℝ} {p : ℂ} (hseq : SeqLimit A q κ D p)
    (hdbl : DoublingCompatible A q e0) {sX : ℕ → ℝ} {τ : ℝ}
    (hτ : Tendsto (fun X : ℕ => sX X * √(Real.log X)) atTop (𝓝 τ)) :
    Tendsto (fun X : ℕ => (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q (sX X) (κ * Real.log n) n) atTop
      (𝓝 ((Real.exp (-(D * τ ^ 2)) : ℂ) * p)) := by
  classical
  set ℓ : ℂ := (Real.exp (-(D * τ ^ 2)) : ℂ) * p with hℓ
  -- the `e`-th two-adic layer
  let T : ℕ → ℕ → ℂ := fun X e => (X : ℂ)⁻¹ *
    ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, ph A q (sX X) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u)
  have hsum : ∀ X : ℕ, (X : ℂ)⁻¹ * ∑ n ∈ Icc 1 X, ph A q (sX X) (κ * Real.log n) n = ∑' e, T X e := by
    intro X
    rw [tsum_eq_sum (s := range (X + 1)), sum_Icc_two_adic, mul_sum]
    intro e he
    simp only [mem_range, not_lt] at he
    have h0 : X / 2 ^ e = 0 :=
      Nat.div_eq_of_lt ((Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right two_pos (by omega)))
    simp [T, h0]
  -- each layer: `T X e → 2^{-e} ℓ / 2`
  have hlayer : ∀ e : ℕ, Tendsto (fun X => T X e) atTop (𝓝 ((1 / 2 : ℂ) ^ e * (ℓ / 2))) := by
    intro e
    have he0 : 0 < 2 ^ e := by positivity
    -- inner average over `[1, Z]`, `Z = ⌊X/2^e⌋`, by dyadic blocks
    have hinner := dyadic_tannery (L := atTop) (Z := fun X : ℕ => X / 2 ^ e)
      (f := fun X u => if Odd u then
        ph A q (sX X) (κ * Real.log ((2 ^ e * u : ℕ) : ℝ)) (2 ^ e * u) else 0)
      (fun X u => by split_ifs <;> simp [norm_ph_le])
      (ℓ := ℓ / 2) (fun k => by
        obtain ⟨n0, hn0⟩ := hdbl.iterate
        simpa [hℓ] using block_limit hseq e k ⟨n0, hn0 e⟩ hτ)
    have hZX : Tendsto (fun X : ℕ => ((((X / 2 ^ e : ℕ) : ℝ) / X : ℝ) : ℂ)) atTop
        (𝓝 (((1 / 2 ^ e : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (by simpa using tendsto_natDiv_div_self he0)
    have := hZX.mul hinner
    have hval : (((1 / 2 ^ e : ℝ)) : ℂ) * (ℓ / 2) = (1 / 2 : ℂ) ^ e * (ℓ / 2) := by
      push_cast; rw [div_pow, one_pow]
    rw [hval] at this
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
  have hgeom : ∑' e : ℕ, (1 / 2 : ℂ) ^ e * (ℓ / 2) = ℓ := by
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one (by norm_num)]; norm_num; ring
  rw [hgeom] at hT
  exact hT.congr' (Eventually.of_forall fun X => (hsum X).symm)

end CollatzCLT
