import LeanClt.Mixing.Pieces

/-!
# §3.2: the near-diagonal estimate (Proposition 3.4, `prop:neardiag`)

* `l1_mix_le_two`: the trivial bound `‖μ_n - Q_m μ_n‖₁ ≤ 2`.
* `neardiag_main`: the estimate for one `n`, given a prefix decomposition, a bound `β` on the
  tail transforms at excluded frequencies and a bound `γ ≥ √(3^n 2^{-l})` (collision):
  `‖μ_n - Q_m μ_n‖₁ ≤ 2δ + (3n+1)·#I·βγ + 4e^{-n/12}`, where `δ` is the mass defect. The counter
  is cut at `3n`; beyond it, Lemma 2.2(i) (`lawS_chernoff`).
* `neardiag`: **Proposition 3.4.** For every `A > 0` there is `C'_A` with
  `‖μ_n - Q_m μ_n‖₁ ≤ C'_A m^{-A}` whenever `0.9 n ≤ m ≤ n` (stated as `9n ≤ 10m`).

Order of constants, as in the paper: fix `A`; take `L = A` in `TaoPrefix` (the paper takes
`L = A + 4`; the mass defect enters only once, so `L = A` suffices), which fixes `C` and
`E = C² log 2`; then `B = A + 3 + E/2` in `TaoMajorant`.

Only the following consequences of `TaoPrefix` are used: the count `#I ≤ K n²`, `D ⊆ words p l`,
the upper bound on `p` (to get `m - p ≥ n/20`), the lower bound on `l` (collision), disjointness,
the mass, and separation. The lower bound on `p`, the upper bound on `l` and `p ≤ n` are not used.
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Elementary estimates -/

/-- `log 3 / (2 log 2) ≤ 4/5`, from `3^5 = 243 ≤ 256 = 2^8`. -/
lemma log3_div_le : Real.log 3 / (2 * Real.log 2) ≤ 4 / 5 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log ((3 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 8) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h1
  push_cast at h1
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `K √(n log n) ≤ n/20` for all large `n`. -/
lemma sqrt_log_le (K : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * √(n * Real.log n) ≤ n / 20 := by
  refine ⟨⌈(800 * K ^ 2) ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  rcases le_or_gt K 0 with hK | hK
  · have : K * √(n * Real.log n) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK (Real.sqrt_nonneg _)
    have : (0 : ℝ) ≤ n / 20 := by positivity
    linarith
  · have hsq : Real.log n ≤ 2 * √n := by
      have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
      rw [Real.log_sqrt hn0.le] at this
      linarith [Real.sqrt_nonneg (n : ℝ)]
    have hbig : 800 * K ^ 2 ≤ √n := by
      rw [Real.le_sqrt (by positivity) hn0.le]
      have : ((⌈(800 * K ^ 2) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      linarith [Nat.le_ceil ((800 * K ^ 2) ^ 2)]
    have hs : √(n : ℝ) * √n = n := Real.mul_self_sqrt hn0.le
    have key : K ^ 2 * (n * Real.log n) ≤ (n / 20) ^ 2 := by
      calc K ^ 2 * (n * Real.log n) ≤ K ^ 2 * (n * (2 * √n)) := by
            gcongr
        _ = n * (2 * K ^ 2 * √n) := by ring
        _ ≤ n * (√n / 400 * √n) := by
            gcongr
            nlinarith [hbig, Real.sqrt_nonneg (n : ℝ)]
        _ = (n / 20) ^ 2 := by
            rw [div_mul_eq_mul_div, hs]; ring
    calc K * √(n * Real.log n) = √(K ^ 2 * (n * Real.log n)) := by
          rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK.le]
      _ ≤ √((n / 20) ^ 2) := Real.sqrt_le_sqrt key
      _ = n / 20 := Real.sqrt_sq (by positivity)

/-- `e^{-x/12} ≤ c x^{-A}` for `x ≥ 1`. -/
lemma exp_neg_le_rpow (A : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, 1 ≤ x → Real.exp (-(x / 12)) ≤ c * x ^ (-A) := by
  set k := ⌈A⌉₊
  refine ⟨(k.factorial : ℝ) * 12 ^ k, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 := Real.pow_div_factorial_le_exp (x / 12) (by positivity) k
  have hk : x ^ (-(k : ℝ)) ≤ x ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [Nat.le_ceil A])
  rw [Real.rpow_neg hx0.le, Real.rpow_natCast] at hk
  rw [Real.exp_neg]
  calc (Real.exp (x / 12))⁻¹ ≤ ((x / 12) ^ k / k.factorial)⁻¹ := inv_anti₀ (by positivity) h1
    _ = k.factorial * 12 ^ k * (x ^ k)⁻¹ := by rw [inv_div, div_pow]; field_simp
    _ ≤ k.factorial * 12 ^ k * x ^ (-A) := by gcongr

/-- **`3^n 2^{-l} ≤ n^{C² log 2}`** when `l ≥ n log₂ 3 - C² log n` (the second half of
(2.7, `eq:collision`)). -/
lemma three_pow_mul_half_pow_le {n l : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hl : (n : ℝ) * Real.logb 2 3 - C ^ 2 * Real.log n ≤ l) :
    (3 : ℝ) ^ n * (1 / 2) ^ l ≤ (n : ℝ) ^ (C ^ 2 * Real.log 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < 3 ^ n * (1 / 2) ^ l := by positivity
  rw [← Real.exp_log hpos, Real.rpow_def_of_pos hn0, Real.exp_le_exp, Real.log_mul
    (by positivity) (by positivity), Real.log_pow, Real.log_pow, one_div, Real.log_inv]
  have := mul_le_mul_of_nonneg_right hl h2.le
  rw [sub_mul, Real.logb, mul_assoc, div_mul_cancel₀ _ h2.ne'] at this
  nlinarith

/-! ## The trivial bound -/

lemma sum_abs_mix_le (n m : ℕ) (hmn : m ≤ n) (s : ℕ) :
    ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤ 2 * lawS n s := by
  calc ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x|
      ≤ ∑ x : ZMod (3 ^ n), (muJ n s x + Qop n m (muJ n) s x) :=
        Finset.sum_le_sum fun x _ => by
          rw [abs_le]
          constructor <;> linarith [muJ_nonneg n s x, Qop_nonneg n m s x]
    _ = 2 * lawS n s := by
        rw [Finset.sum_add_distrib, Qop_mass hmn, sum_muJ]; ring

/-- **The trivial bound** `‖μ_n - Q_m μ_n‖₁ ≤ 2`. -/
lemma l1_mix_le_two (n m : ℕ) (hmn : m ≤ n) :
    ∑' s, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤ 2 := by
  calc _ ≤ ∑' s, 2 * lawS n s :=
        Summable.tsum_le_tsum (sum_abs_mix_le n m hmn) (summable_mix n m hmn)
          ((summable_lawS n).mul_left 2)
    _ = 2 := by rw [tsum_mul_left, tsum_lawS, mul_one]

/-! ## The estimate for one `n` -/

open Classical in
/-- **Proposition 3.4 for one `n`**, from a prefix decomposition. -/
theorem neardiag_main {n m : ℕ} (hn1 : 1 ≤ n) (hmn : m ≤ n) (I : Finset (ℕ × ℕ))
    (D : (p : ℕ) → ℕ → Finset (Fin p → ℕ))
    (hsub : ∀ pl ∈ I, D pl.1 pl.2 ⊆ words pl.1 pl.2)
    (hdisj : ∀ pl ∈ I, ∀ pl' ∈ I, pl ≠ pl' → ∀ h : pl.1 ≤ pl'.1, ∀ w ∈ D pl'.1 pl'.2,
      prefixOf h w ∉ D pl.1 pl.2)
    {δ : ℝ} (hmass : 1 - δ ≤ ∑ pl ∈ I, ((D pl.1 pl.2).card : ℝ) * (1 / 2 : ℝ) ^ pl.2)
    (hinj : ∀ pl ∈ I, Set.InjOn (XmodN n) (↑(D pl.1 pl.2) : Set (Fin pl.1 → ℕ)))
    (hpn : ∀ pl ∈ I, pl.1 ≤ n)
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : ∀ pl ∈ I, √((3 : ℝ) ^ n * (1 / 2) ^ pl.2) ≤ γ)
    (hT : ∀ pl ∈ I, ∀ ξ : ZMod (3 ^ n), ξ * 3 ^ m ≠ 0 → ∀ s' : ℕ,
      ‖(1 / 2 : ℂ) ^ s' * ∑ v ∈ words (n - pl.1) s',
        chiZ ξ (3 ^ pl.1 * half n ^ pl.2 * XmodN n v)‖ ≤ β) :
    ∑' s, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤
      2 * δ + (3 * n + 1) * (I.card * (β * γ)) + 4 * Real.exp (-(n / 12)) := by
  set g : ℕ × ℕ → ℕ → ZMod (3 ^ n) → ℝ := fun pl => gP n pl.1 (D pl.1 pl.2) with hg
  set R : ℕ → ZMod (3 ^ n) → ℝ := fun s y => muJ n s y - ∑ pl ∈ I, g pl s y with hR
  have hR0 : ∀ s y, 0 ≤ R s y := fun s y => sub_nonneg.mpr (sum_gP_le_muJ n I D hdisj s y)
  have hqn : ∀ pl ∈ I, pl.1 + (n - pl.1) = n := fun pl hpl => by have := hpn pl hpl; omega
  -- each piece, each slice
  have hpiece : ∀ pl ∈ I, ∀ s, ∑ x : ZMod (3 ^ n), |g pl s x - Qop n m (g pl) s x| ≤ β * γ := by
    intro pl hpl s
    refine (piece_slice_bound (hqn pl hpl) hmn _ (hsub pl hpl) (hinj pl hpl) hβ (hT pl hpl) s).trans
      ?_
    exact mul_le_mul_of_nonneg_left (hγ pl hpl) hβ
  -- decomposition of one slice
  have hμ : (fun s y => R s y + ∑ pl ∈ I, g pl s y) = muJ n := by
    funext s y; simp only [hR]; ring
  have hdec : ∀ s, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤
      2 * ∑ x : ZMod (3 ^ n), R s x + I.card * (β * γ) := by
    intro s
    have hQ : ∀ x, Qop n m (muJ n) s x = Qop n m R s x + ∑ pl ∈ I, Qop n m (g pl) s x := by
      intro x; rw [← hμ]; exact Qop_add_sum I R g s x
    have hpt : ∀ x, |muJ n s x - Qop n m (muJ n) s x| ≤ (R s x + Qop n m R s x) +
        ∑ pl ∈ I, |g pl s x - Qop n m (g pl) s x| := by
      intro x
      have e : muJ n s x - Qop n m (muJ n) s x =
          (R s x - Qop n m R s x) + ∑ pl ∈ I, (g pl s x - Qop n m (g pl) s x) := by
        rw [hQ, Finset.sum_sub_distrib]; simp only [hR]; ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ (Finset.abs_sum_le_sum_abs _ _))
      have h1 := hR0 s x
      have h2 := Qop_nonneg_of (m := m) (fun y => hR0 s y) x
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ x : ZMod (3 ^ n), ((R s x + Qop n m R s x) +
          ∑ pl ∈ I, |g pl s x - Qop n m (g pl) s x|) := Finset.sum_le_sum fun x _ => hpt x
      _ = 2 * ∑ x : ZMod (3 ^ n), R s x +
            ∑ pl ∈ I, ∑ x : ZMod (3 ^ n), |g pl s x - Qop n m (g pl) s x| := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Qop_mass hmn, Finset.sum_comm]
          ring
      _ ≤ 2 * ∑ x : ZMod (3 ^ n), R s x + ∑ pl ∈ I, β * γ := by
          gcongr with pl hpl; exact hpiece pl hpl s
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the mass defect
  have hgsum : ∀ pl ∈ I, Summable (fun s => ∑ y : ZMod (3 ^ n), g pl s y) ∧
      ∑' s, ∑ y : ZMod (3 ^ n), g pl s y = ((D pl.1 pl.2).card : ℝ) * (1 / 2) ^ pl.2 :=
    fun pl hpl => tsum_gP (hqn pl hpl) _ (hsub pl hpl)
  have hRs : (fun s => ∑ x : ZMod (3 ^ n), R s x) =
      fun s => lawS n s - ∑ pl ∈ I, ∑ y : ZMod (3 ^ n), g pl s y := by
    funext s
    simp only [hR]
    rw [Finset.sum_sub_distrib, sum_muJ, Finset.sum_comm]
  have hsumG : Summable (fun s => ∑ pl ∈ I, ∑ y : ZMod (3 ^ n), g pl s y) :=
    summable_sum fun pl hpl => (hgsum pl hpl).1
  have hRsum : Summable (fun s => ∑ x : ZMod (3 ^ n), R s x) := by
    rw [hRs]; exact (summable_lawS n).sub hsumG
  have hRt : ∑' s, ∑ x : ZMod (3 ^ n), R s x ≤ δ := by
    rw [hRs, (summable_lawS n).tsum_sub hsumG, tsum_lawS,
      Summable.tsum_finsetSum (fun pl hpl => (hgsum pl hpl).1),
      Finset.sum_congr rfl (fun pl hpl => (hgsum pl hpl).2)]
    linarith
  -- cutting the counter at `3n`
  set f : ℕ → ℝ := fun s => ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| with hf
  have hf0 : ∀ s, 0 ≤ f s := fun s => Finset.sum_nonneg fun x _ => abs_nonneg _
  have hfs : Summable f := summable_mix n m hmn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfle : ∀ s, f s ≤ (if s ≤ 3 * n then f s else 0) +
      2 * (if (n : ℝ) ≤ |(s : ℝ) - 2 * n| then lawS n s else 0) := by
    intro s
    by_cases h1 : s ≤ 3 * n
    · rw [if_pos h1]
      have : 0 ≤ 2 * (if (n : ℝ) ≤ |(s : ℝ) - 2 * n| then lawS n s else 0) := by
        split_ifs <;> simp [lawS_nonneg]
      linarith
    · rw [if_neg h1, zero_add]
      have h2 : (n : ℝ) ≤ |(s : ℝ) - 2 * n| := by
        have : (3 * n : ℝ) < s := by exact_mod_cast (show 3 * n < s by omega)
        rw [abs_of_pos (by linarith)]; linarith
      rw [if_pos h2]
      exact sum_abs_mix_le n m hmn s
  have hs1 : Summable (fun s => if s ≤ 3 * n then f s else 0) :=
    Summable.of_nonneg_of_le (fun s => by split_ifs <;> simp [hf0])
      (fun s => by split_ifs <;> simp [hf0]) hfs
  have hs2 := summable_ite_lawS n (fun s : ℕ => (n : ℝ) ≤ |(s : ℝ) - 2 * n|)
  have hcut : ∑' s, (if s ≤ 3 * n then f s else 0) = ∑ s ∈ range (3 * n + 1), f s := by
    rw [tsum_eq_sum (s := range (3 * n + 1))]
    · exact Finset.sum_congr rfl fun s hs => if_pos (by have := mem_range.mp hs; omega)
    · intro s hs; rw [if_neg (by rw [mem_range] at hs; omega)]
  have hch : ∑' s : ℕ, (if (n : ℝ) ≤ |(s : ℝ) - 2 * n| then lawS n s else 0) ≤
      2 * Real.exp (-(n / 12)) := by
    have := lawS_chernoff hn1 (x := (n : ℝ)) hn0.le
    have hmin : min ((n : ℝ) ^ 2 / (12 * n)) ((n : ℝ) / 8) = (n : ℝ) / 12 := by
      rw [show (n : ℝ) ^ 2 / (12 * n) = (n : ℝ) / 12 by field_simp]
      exact min_eq_left (by linarith)
    rwa [hmin] at this
  have hfin : ∑ s ∈ range (3 * n + 1), ∑ x : ZMod (3 ^ n), R s x ≤ δ :=
    (hRsum.sum_le_tsum _ (fun s _ => Finset.sum_nonneg fun x _ => hR0 s x)).trans hRt
  calc ∑' s, f s ≤ ∑' s, ((if s ≤ 3 * n then f s else 0) +
        2 * (if (n : ℝ) ≤ |(s : ℝ) - 2 * n| then lawS n s else 0)) :=
        Summable.tsum_le_tsum hfle hfs (hs1.add (hs2.mul_left 2))
    _ = ∑ s ∈ range (3 * n + 1), f s +
          2 * ∑' s : ℕ, (if (n : ℝ) ≤ |(s : ℝ) - 2 * n| then lawS n s else 0) := by
        rw [Summable.tsum_add hs1 (hs2.mul_left 2), tsum_mul_left, hcut]
    _ ≤ ∑ s ∈ range (3 * n + 1), (2 * ∑ x : ZMod (3 ^ n), R s x + I.card * (β * γ)) +
          2 * (2 * Real.exp (-(n / 12))) := by
        gcongr with s hs
        exact hdec s
    _ = 2 * ∑ s ∈ range (3 * n + 1), ∑ x : ZMod (3 ^ n), R s x +
          (3 * n + 1) * (I.card * (β * γ)) + 4 * Real.exp (-(n / 12)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 2 * δ + (3 * n + 1) * (I.card * (β * γ)) + 4 * Real.exp (-(n / 12)) := by
        gcongr

/-! ## Proposition 3.4 -/

/-- **Proposition 3.4 (`prop:neardiag`).** For every `A > 0` there is `C'_A` such that
`‖μ_n - Q_m μ_n‖₁ ≤ C'_A m^{-A}` whenever `0.9 n ≤ m ≤ n` (here `9n ≤ 10m`). -/
theorem neardiag (hTM : TaoMajorant) (hTP : TaoPrefix) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ m n : ℕ, 1 ≤ m → m ≤ n → 9 * n ≤ 10 * m →
      ∑' s, ∑ x : ZMod (3 ^ n), |muJ n s x - Qop n m (muJ n) s x| ≤ C * (m : ℝ) ^ (-A) := by
  obtain ⟨C, K, n₀, hP⟩ := hTP A hA
  set E : ℝ := C ^ 2 * Real.log 2 with hE
  have hE0 : 0 ≤ E := mul_nonneg (sq_nonneg C) (Real.log_nonneg (by norm_num))
  set B : ℝ := A + 3 + E / 2 with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  obtain ⟨Cc, hCc⟩ := conductor_bound hTM hB
  obtain ⟨c₁, hc₁0, hc₁⟩ := exp_neg_le_rpow A
  obtain ⟨N₁, hN₁⟩ := sqrt_log_le K
  set N : ℕ := max (max n₀ N₁) 1 with hN
  set Cc' : ℝ := max Cc 0 with hCc'
  have hCc'0 : 0 ≤ Cc' := le_max_right _ _
  set C₀ : ℝ := 2 * |K| + 4 * |K| * Cc' * 20 ^ B + 4 * c₁ with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨max C₀ (2 * (N : ℝ) ^ A), fun m n hm hmn h9 => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmA : 0 < (m : ℝ) ^ (-A) := Real.rpow_pos_of_pos hm0 _
  by_cases hnN : n < N
  · -- small `n`: the trivial bound
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
    have h1 : 1 ≤ (N : ℝ) ^ A * (m : ℝ) ^ (-A) := by
      rw [Real.rpow_neg hm0.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hm0 _)]
      exact Real.rpow_le_rpow hm0.le hmN hA.le
    calc _ ≤ 2 := l1_mix_le_two n m hmn
      _ ≤ 2 * ((N : ℝ) ^ A * (m : ℝ) ^ (-A)) := by linarith
      _ = 2 * (N : ℝ) ^ A * (m : ℝ) ^ (-A) := by ring
      _ ≤ max C₀ (2 * (N : ℝ) ^ A) * (m : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hmA.le
  · push Not at hnN
    have hn₀ : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
    have hN₁n : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hnN
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨I, D, hcard, hsub, hp, hl, hdisj, hmass, hinj⟩ := hP n hn₀
    -- the prefix ends well before `m`
    have hpm : ∀ pl ∈ I, (pl.1 : ℝ) + n / 20 ≤ m := by
      intro pl hpl
      have h1 := hp pl hpl
      have h2 := hN₁ n hN₁n
      have h3 : Real.log 3 / (2 * Real.log 2) * n ≤ 4 / 5 * n :=
        mul_le_mul_of_nonneg_right log3_div_le hn0.le
      have h4 : (9 : ℝ) * n ≤ 10 * m := by exact_mod_cast h9
      linarith
    have hpm' : ∀ pl ∈ I, pl.1 ≤ m := fun pl hpl => by
      have h1 := hpm pl hpl
      have : (pl.1 : ℝ) ≤ m := by linarith [show (0 : ℝ) ≤ n / 20 by positivity]
      exact_mod_cast this
    have hpn : ∀ pl ∈ I, pl.1 ≤ n := fun pl hpl => (hpm' pl hpl).trans hmn
    -- the tail bound `β` at excluded frequencies (Corollary 3.3)
    set β : ℝ := Cc' * ((n : ℝ) / 20) ^ (-B) with hβdef
    have hβ0 : 0 ≤ β := mul_nonneg hCc'0 (Real.rpow_nonneg (by positivity) _)
    have hT : ∀ pl ∈ I, ∀ ξ : ZMod (3 ^ n), ξ * 3 ^ m ≠ 0 → ∀ s' : ℕ,
        ‖(1 / 2 : ℂ) ^ s' * ∑ v ∈ words (n - pl.1) s',
          chiZ ξ (3 ^ pl.1 * half n ^ pl.2 * XmodN n v)‖ ≤ β := by
      intro pl hpl ξ hξ s'
      obtain ⟨r, hr, hrq, ζ, hζ, hchi⟩ := tail_char_reduce pl.2
        (show pl.1 + (n - pl.1) = n by have := hpn pl hpl; omega) (hpm' pl hpl) hmn ξ hξ
      have hrR : (n : ℝ) / 20 ≤ r := by
        have h1 := hpm pl hpl
        have h2 : ((m - pl.1 : ℕ) : ℝ) = m - pl.1 := by rw [Nat.cast_sub (hpm' pl hpl)]
        have h3 : ((m - pl.1 : ℕ) : ℝ) < r := by exact_mod_cast hr
        linarith
      have hr1 : 1 ≤ r := by
        have : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrR
        exact_mod_cast this
      obtain ⟨hs, hb⟩ := hCc r (n - pl.1) hr1 hrq ζ hζ
      simp_rw [hchi]
      calc _ ≤ ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ v ∈ words (n - pl.1) s,
            chiZ ζ (ZMod.cast (Xmod v) : ZMod (3 ^ r))‖ :=
            hs.le_tsum s' (fun _ _ => norm_nonneg _)
        _ ≤ Cc * (r : ℝ) ^ (-B) := hb
        _ ≤ Cc' * (r : ℝ) ^ (-B) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
        _ ≤ β := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by positivity) hrR (by linarith)) hCc'0
    -- the collision bound `γ`
    set γ : ℝ := (n : ℝ) ^ (E / 2) with hγdef
    have hγ : ∀ pl ∈ I, √((3 : ℝ) ^ n * (1 / 2) ^ pl.2) ≤ γ := by
      intro pl hpl
      calc √((3 : ℝ) ^ n * (1 / 2) ^ pl.2) ≤ √((n : ℝ) ^ E) :=
            Real.sqrt_le_sqrt (three_pow_mul_half_pow_le hn1 (hl pl hpl))
        _ = γ := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le, hγdef]; ring_nf
    have hmain := neardiag_main hn1 hmn I D hsub hdisj hmass hinj hpn hβ0 hγ hT
    -- arithmetic
    have hnA : (n : ℝ) ^ (-A) ≤ (m : ℝ) ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hmn) (by linarith)
    have hkey : (n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-B) * (n : ℝ) ^ (E / 2) = (n : ℝ) ^ (-A) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, hBdef]; congr 1; ring
    have hβeq : β = Cc' * 20 ^ B * (n : ℝ) ^ (-B) := by
      rw [hβdef, Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 20)]
      field_simp
    have hcardK : (I.card : ℝ) ≤ |K| * (n : ℝ) ^ 2 :=
      hcard.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
    have hmid : (3 * (n : ℝ) + 1) * (I.card * (β * γ)) ≤
        4 * |K| * Cc' * 20 ^ B * (n : ℝ) ^ (-A) := by
      have hβγ : 0 ≤ β * γ := mul_nonneg hβ0 (Real.rpow_nonneg hn0.le _)
      calc (3 * (n : ℝ) + 1) * (I.card * (β * γ)) ≤ (4 * n) * ((|K| * n ^ 2) * (β * γ)) := by
            gcongr; linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1]
        _ = 4 * |K| * Cc' * 20 ^ B *
              ((n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-B) * (n : ℝ) ^ (E / 2)) := by
            rw [hβeq, hγdef, show (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 : ℕ) by norm_cast]; ring
        _ = _ := by rw [hkey]
    have hδ : 2 * (K * (n : ℝ) ^ (-A)) ≤ 2 * |K| * (n : ℝ) ^ (-A) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hn0.le (-A))
      linarith
    have hexp : 4 * Real.exp (-((n : ℝ) / 12)) ≤ 4 * c₁ * (n : ℝ) ^ (-A) := by
      have := hc₁ n (by exact_mod_cast hn1); linarith
    calc _ ≤ 2 * (K * (n : ℝ) ^ (-A)) + (3 * n + 1) * (I.card * (β * γ)) +
          4 * Real.exp (-(n / 12)) := hmain
      _ ≤ C₀ * (n : ℝ) ^ (-A) := by rw [hC₀]; linarith
      _ ≤ C₀ * (m : ℝ) ^ (-A) := mul_le_mul_of_nonneg_left hnA hC₀0
      _ ≤ max C₀ (2 * (N : ℝ) ^ A) * (m : ℝ) ^ (-A) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hmA.le

end CollatzCLT
