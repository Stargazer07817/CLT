import LeanClt.Renewal.RotationCount

/-!
# Lemma 2.7 [`lem:rotation`] (rotation discrepancy)

Assuming Rhin's irrationality measure for `θ = log₂ 3`, with `ε = 1/(ϰ+1)`:
`|∑_{j=1}^N q(γ + jθ) - N ∫₀¹ q| ≤ C (M + L) N^{1-ε}` uniformly in `γ` and `N ≥ 1`, for every
`1`-periodic `q` bounded by `M` and `L`-Lipschitz on each period cell.

The proof is the paper's:
* choose `Q = N^{1-ε}`, and let Dirichlet's theorem give a reduced `p/K` with `K ≤ Q` and
  `|θ - p/K| ≤ 1/(KQ)`;
* Rhin forces `K ≥ (dQ)^{1/ϰ} = d^{1/ϰ} N^ε`;
* split into `⌊N/K⌋` blocks of length `K` (each handled by `block_bound`) plus a remainder;
* every error is `O((M + L) N^{1-ε})`.
-/

open Real Finset

namespace CollatzCLT

/-- A sum over `[0, bK)` is a sum of `b` blocks of length `K`. -/
lemma sum_range_mul_blocks {β : Type*} [AddCommMonoid β] (g : ℕ → β) (K : ℕ) :
    ∀ b : ℕ, ∑ j ∈ range (b * K), g j = ∑ t ∈ range b, ∑ i ∈ range K, g (t * K + i) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- **Lemma 2.7 [`lem:rotation`] (rotation discrepancy).** -/
theorem rotation_discrepancy {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C : ℝ, ∀ (q : ℝ → ℂ) (M L x₀ : ℝ), (∀ x, q (x + 1) = q x) → (∀ x, ‖q x‖ ≤ M) →
      (∀ x y, x₀ < x → x ≤ x₀ + 1 → x₀ < y → y ≤ x₀ + 1 → ‖q x - q y‖ ≤ L * |x - y|) →
      ∀ (γ : ℝ) (N : ℕ), 1 ≤ N →
        ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * ∫ x in (0 : ℝ)..1, q x‖ ≤
          C * (M + L) * (N : ℝ) ^ (1 - 1 / (ϰ + 1)) := by
  obtain ⟨hd, hϰ, hrhin⟩ := hθ
  set ε : ℝ := 1 / (ϰ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε2 : ε ≤ 1 / 2 := by rw [hε, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  refine ⟨12 * d ^ (-(1 / ϰ)) + 14, ?_⟩
  intro q M L x₀ hper hbdd hlip γ N hN
  have hq : PiecewiseLip q M L x₀ := ⟨hper, hbdd, hlip⟩
  have hM := hq.M_nonneg
  have hL := hq.L_nonneg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hdpow : 0 ≤ d ^ (-(1 / ϰ)) := Real.rpow_nonneg hd.le _
  set I := ∫ x in (0 : ℝ)..1, q x with hIdef
  have hI : ‖I‖ ≤ M := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := q) (C := M) (fun x _ => hbdd x)
    simpa using this
  set Q : ℝ := (N : ℝ) ^ (1 - ε) with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hN1 (by linarith)
  -- the trivial bound `2MN`
  have htriv : ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * I‖ ≤ 2 * M * N := by
    calc ‖∑ j ∈ Icc 1 N, q (γ + j * θ) - N * I‖ ≤ ‖∑ j ∈ Icc 1 N, q (γ + j * θ)‖ + ‖(N : ℂ) * I‖ :=
          norm_sub_le _ _
      _ ≤ N * M + N * M := by
          gcongr
          · calc ‖∑ j ∈ Icc 1 N, q (γ + j * θ)‖ ≤ ∑ j ∈ Icc 1 N, ‖q (γ + j * θ)‖ := norm_sum_le _ _
              _ ≤ ∑ j ∈ Icc 1 N, M := sum_le_sum fun j _ => hbdd _
              _ = N * M := by simp
          · rw [norm_mul, Complex.norm_natCast]; gcongr
      _ = 2 * M * N := by ring
  rcases lt_or_ge Q 2 with hQ2 | hQ2
  · -- small `N`: `N^{1/2} ≤ Q < 2`, so `N < 4`
    have hsq : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ Q := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hN4 : (N : ℝ) < 4 := by
      have h := lt_of_le_of_lt hsq hQ2
      have : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      nlinarith [Real.rpow_nonneg hN0.le ((1 : ℝ) / 2)]
    calc _ ≤ 2 * M * N := htriv
      _ ≤ 8 * M := by nlinarith
      _ ≤ (12 * d ^ (-(1 / ϰ)) + 14) * (M + L) * 1 := by nlinarith
      _ ≤ (12 * d ^ (-(1 / ϰ)) + 14) * (M + L) * Q := by gcongr
  -- main case: Dirichlet approximation with denominator `K ≤ ⌊Q⌋`
  set n := ⌊Q⌋₊ with hn
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hQ2)
  obtain ⟨r, hr1, hr2⟩ := Real.exists_rat_abs_sub_le_and_den_le θ (n := n) (by omega)
  set K := r.den with hKdef
  set p := r.num with hpdef
  have hK1 : 1 ≤ K := r.den_pos
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKn : (K : ℝ) ≤ Q := le_trans (by exact_mod_cast hr2) (Nat.floor_le (by linarith))
  have hQn : Q < n + 1 := Nat.lt_floor_add_one Q
  have hrcast : (r : ℝ) = p / K := Rat.cast_def r
  have happrox : |θ - p / K| ≤ 1 / (K * Q) := by
    rw [← hrcast]
    refine hr1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- `u p + v K = 1`
  obtain ⟨u, v, huv⟩ : IsCoprime p (K : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa using r.reduced
  -- Rhin: `d K^{-ϰ} ≤ ‖Kθ‖ ≤ 1/Q`, hence `K ≥ d^{1/ϰ} N^ε`
  have hrh := hrhin K hK1
  have hdist : distZ (K * θ) ≤ 1 / Q := by
    unfold distZ
    calc |(K : ℝ) * θ - round ((K : ℝ) * θ)| ≤ |(K : ℝ) * θ - p| := round_le _ p
      _ = K * |θ - p / K| := by
          rw [show (K : ℝ) * θ - p = K * (θ - p / K) by field_simp, abs_mul, abs_of_pos hK0]
      _ ≤ K * (1 / (K * Q)) := by gcongr
      _ = 1 / Q := by field_simp
  have hKpow : d * Q ≤ (K : ℝ) ^ ϰ := by
    have h1 : d * (K : ℝ) ^ (-ϰ) ≤ 1 / Q := hrh.trans hdist
    rw [Real.rpow_neg hK0.le] at h1
    have hKϰ : 0 < (K : ℝ) ^ ϰ := Real.rpow_pos_of_pos hK0 _
    rw [mul_inv_le_iff₀ hKϰ] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ Q)
    calc d * Q ≤ 1 / Q * (K : ℝ) ^ ϰ * Q := h2
      _ = (K : ℝ) ^ ϰ := by field_simp
  have hKlow : d ^ (1 / ϰ) * (N : ℝ) ^ ε ≤ K := by
    have hϰ0 : 0 < ϰ := by linarith
    have h1 : (d * Q) ^ (1 / ϰ) ≤ ((K : ℝ) ^ ϰ) ^ (1 / ϰ) :=
      Real.rpow_le_rpow (by positivity) hKpow (by positivity)
    rw [← Real.rpow_mul hK0.le, mul_one_div_cancel hϰ0.ne', Real.rpow_one,
      Real.mul_rpow hd.le (by positivity), hQ, ← Real.rpow_mul hN0.le] at h1
    have : (1 - ε) * (1 / ϰ) = ε := by rw [hε]; field_simp; ring
    rwa [this] at h1
  have hNK : (N : ℝ) / K ≤ d ^ (-(1 / ϰ)) * Q := by
    have hdpos : 0 < d ^ (1 / ϰ) := Real.rpow_pos_of_pos hd _
    have hNε : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hN0 _
    rw [div_le_iff₀ hK0]
    have hsplit : (N : ℝ) = (N : ℝ) ^ ε * Q := by
      rw [hQ, ← Real.rpow_add hN0]; simp
    have hinv : d ^ (-(1 / ϰ)) * d ^ (1 / ϰ) = 1 := by
      rw [← Real.rpow_add hd]; simp
    calc (N : ℝ) = d ^ (-(1 / ϰ)) * Q * (d ^ (1 / ϰ) * (N : ℝ) ^ ε) := by
          rw [mul_comm (d ^ (-(1 / ϰ))) Q, mul_assoc, ← mul_assoc (d ^ (-(1 / ϰ))), hinv, one_mul,
            mul_comm Q, ← hsplit]
      _ ≤ d ^ (-(1 / ϰ)) * Q * K := by gcongr
  have hNQ : (N : ℝ) / Q ≤ Q := by
    rw [div_le_iff₀ (by linarith), hQ, ← Real.rpow_add hN0]
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1 - ε + (1 - ε)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- split into `b` blocks and a remainder
  set b := N / K with hb
  set r0 := N % K with hr0
  have hNbr : N = b * K + r0 := by rw [hb, hr0, mul_comm]; exact (Nat.div_add_mod N K).symm
  have hr0K : (r0 : ℝ) ≤ K := by exact_mod_cast (Nat.mod_lt N (by omega)).le
  have hbK : (b : ℝ) ≤ N / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast Nat.div_mul_le_self N K
  set g : ℕ → ℂ := fun j => q (γ + θ + j * θ) with hg
  have hshift : ∑ j ∈ Icc 1 N, q (γ + j * θ) = ∑ j ∈ range N, g j := by
    rw [show Icc 1 N = Ico 1 (N + 1) by ext; simp, sum_Ico_eq_sum_range]
    simp only [hg, Nat.add_sub_cancel]
    apply sum_congr rfl; intro j _; congr 1; push_cast; ring
  have hdecomp : ∑ j ∈ range N, g j - N * I =
      ∑ t ∈ range b, (∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I) +
        (∑ i ∈ range r0, g (b * K + i) - r0 * I) := by
    rw [hNbr, sum_range_add, sum_range_mul_blocks, sum_sub_distrib]
    simp only [hg]
    push_cast
    have : ∀ t i : ℕ, q (γ + θ + ((t : ℝ) * K + i) * θ) = q (γ + θ + (t : ℝ) * K * θ + i * θ) := by
      intro t i; congr 1; ring
    simp_rw [this]
    rw [sum_const, card_range, nsmul_eq_mul]
    ring
  -- block and remainder bounds
  set B : ℝ := (L + 2 * M) + K * L / Q + 2 * M * (3 * (2 * (1 / Q) * K + 1)) with hB
  have hblock : ∀ t ∈ range b,
      ‖∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I‖ ≤ B :=
    fun t _ => hq.block_bound hK1 huv hQ2 happrox _
  have hrem : ‖∑ i ∈ range r0, g (b * K + i) - r0 * I‖ ≤ 2 * M * K := by
    calc ‖∑ i ∈ range r0, g (b * K + i) - r0 * I‖ ≤ r0 * M + r0 * M := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · calc ‖∑ i ∈ range r0, g (b * K + i)‖ ≤ ∑ i ∈ range r0, ‖g (b * K + i)‖ := norm_sum_le _ _
              _ ≤ ∑ i ∈ range r0, M := sum_le_sum fun i _ => hbdd _
              _ = r0 * M := by simp
          · rw [norm_mul, Complex.norm_natCast]; gcongr
      _ ≤ 2 * M * K := by nlinarith
  rw [hshift, hdecomp]
  have hBnn : 0 ≤ B := by positivity
  calc ‖∑ t ∈ range b, (∑ i ∈ range K, q ((γ + θ + (t * K : ℕ) * θ) + i * θ) - K * I) +
        (∑ i ∈ range r0, g (b * K + i) - r0 * I)‖
      ≤ ∑ t ∈ range b, B + 2 * M * K := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (sum_le_sum hblock)) hrem)
    _ = b * B + 2 * M * K := by simp
    _ ≤ (N / K) * B + 2 * M * Q := by gcongr
    _ = (N / K) * (L + 8 * M) + (N / Q) * (L + 12 * M) + 2 * M * Q := by
        rw [hB]; field_simp; ring
    _ ≤ (d ^ (-(1 / ϰ)) * Q) * (L + 8 * M) + Q * (L + 12 * M) + 2 * M * Q := by gcongr
    _ ≤ (12 * d ^ (-(1 / ϰ)) + 14) * (M + L) * Q := by nlinarith

end CollatzCLT
