import LeanClt.Renewal.Rotation

/-!
# Lemma 2.7 [`lem:rotation`], part 2: counting lemmas

* `card_near_le`: at most `2rK + 1` of the points `c + k/K` (`k < K`) lie within `r` of a given `m`.
* `card_near_int_le`: at most `3(2rK + 1)` of them lie within `r ≤ 1/2` of some integer.
* `exists_int_near_of_ceil_ne`: if `|x - y| ≤ r` and `x, y` lie in different cells, then `y` is
  within `r` of a jump point `x₀ + m`.
* `sum_mul_emod_perm`: if `u p ≡ 1 (mod K)`, then `i ↦ i p mod K` permutes `{0, …, K-1}`.
-/

open Real Finset

namespace CollatzCLT

/-- An arithmetic progression of step `1/K` has at most `2rK + 1` points in an interval of
length `2r`. -/
lemma card_near_le {K : ℕ} (hK : 1 ≤ K) (c m : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((range K).filter (fun k : ℕ => |c + k / K - m| ≤ r)).card : ℝ) ≤ 2 * r * K + 1 := by
  classical
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set S := (range K).filter (fun k : ℕ => |c + k / K - m| ≤ r)
  set lo : ℝ := K * (m - c) - r * K
  set hi : ℝ := K * (m - c) + r * K
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp; positivity
  -- every element lies in `[lo, hi]`
  have hmem : ∀ k ∈ S, lo ≤ k ∧ (k : ℝ) ≤ hi := by
    intro k hk
    rw [Finset.mem_filter, abs_le] at hk
    obtain ⟨_, h1, h2⟩ := hk
    have e : (k : ℝ) = K * (c + k / K - m) + K * (m - c) := by field_simp; ring
    constructor <;> rw [e] <;> nlinarith
  obtain ⟨k0, hk0⟩ := hS
  have hhi : 0 ≤ hi := le_trans (Nat.cast_nonneg k0) (hmem k0 hk0).2
  have hsub : S ⊆ Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
    intro k hk
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr (hmem k hk).1, Nat.le_floor (hmem k hk).2⟩
  have hcard : (S.card : ℝ) ≤ ((⌊hi⌋₊ + 1 - ⌈lo⌉₊ : ℕ) : ℝ) := by
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast this
  refine hcard.trans ?_
  rcases le_or_gt (⌊hi⌋₊ + 1) ⌈lo⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp; positivity
  · rw [Nat.cast_sub h.le]
    push_cast
    have h1 : (⌊hi⌋₊ : ℝ) ≤ hi := Nat.floor_le hhi
    have h2 : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
    linarith

open Classical in
/-- At most `3(2rK + 1)` of the points `c + k/K` (`k < K`) lie within `r ≤ 1/2` of an integer. -/
lemma card_near_int_le {K : ℕ} (hK : 1 ≤ K) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 1 / 2) :
    (((range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - m| ≤ r)).card : ℝ) ≤
      3 * (2 * r * K + 1) := by
  classical
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  -- the only candidate integers are `⌊c⌋, ⌊c⌋ + 1, ⌊c⌋ + 2`
  have hsub : (range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - m| ≤ r) ⊆
      (range 3).biUnion (fun j => (range K).filter
        (fun k : ℕ => |c + k / K - ((⌊c⌋ + j : ℤ) : ℝ)| ≤ r)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hkK, m, hm⟩ := hk
    rw [Finset.mem_range] at hkK
    have hk1 : (k : ℝ) / K < 1 := by
      rw [div_lt_one hK']; exact_mod_cast hkK
    have hk0 : (0 : ℝ) ≤ k / K := by positivity
    rw [abs_le] at hm
    have hfl := Int.floor_le c
    have hfl2 := Int.lt_floor_add_one c
    have hlo : ⌊c⌋ ≤ m := by
      have : (⌊c⌋ : ℝ) - 1 < m := by linarith [hm.2]
      have : ⌊c⌋ - 1 < m := by exact_mod_cast this
      omega
    have hhi : m ≤ ⌊c⌋ + 2 := by
      have : (m : ℝ) < ⌊c⌋ + 3 := by linarith [hm.1]
      have : m < ⌊c⌋ + 3 := by exact_mod_cast this
      omega
    rw [Finset.mem_biUnion]
    refine ⟨(m - ⌊c⌋).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hkK, ?_⟩
    have : (⌊c⌋ + ((m - ⌊c⌋).toNat : ℤ) : ℤ) = m := by omega
    rw [this, abs_le]; exact hm
  calc (((range K).filter (fun k : ℕ => ∃ m : ℤ, |c + k / K - m| ≤ r)).card : ℝ)
      ≤ (((range 3).biUnion (fun j => (range K).filter
          (fun k : ℕ => |c + k / K - ((⌊c⌋ + j : ℤ) : ℝ)| ≤ r))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ j ∈ range 3, (((range K).filter
          (fun k : ℕ => |c + k / K - ((⌊c⌋ + j : ℤ) : ℝ)| ≤ r)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ j ∈ range 3, (2 * r * K + 1) := sum_le_sum fun j _ => card_near_le hK c _ hr
    _ = 3 * (2 * r * K + 1) := by simp; ring

/-- If `|x - y| ≤ r` and `x, y` lie in different cells, then `y - x₀` is within `r` of an integer. -/
lemma exists_int_near_of_ceil_ne {x y x₀ r : ℝ} (hxy : |x - y| ≤ r)
    (hne : ⌈x - x₀⌉ ≠ ⌈y - x₀⌉) : ∃ m : ℤ, |y - x₀ - m| ≤ r := by
  rcases le_total (x - x₀) (y - x₀) with h | h
  · -- `⌈x - x₀⌉ < ⌈y - x₀⌉`, so `m = ⌈x - x₀⌉` lies in `[x - x₀, y - x₀)`
    have hlt : ⌈x - x₀⌉ < ⌈y - x₀⌉ := lt_of_le_of_ne (Int.ceil_mono h) hne
    refine ⟨⌈x - x₀⌉, ?_⟩
    have h1 := Int.le_ceil (x - x₀)
    have h2 : ((⌈x - x₀⌉ : ℤ) : ℝ) < y - x₀ := Int.lt_ceil.mp hlt
    rw [abs_le] at hxy ⊢; constructor <;> linarith
  · have hlt : ⌈y - x₀⌉ < ⌈x - x₀⌉ := lt_of_le_of_ne (Int.ceil_mono h) (Ne.symm hne)
    refine ⟨⌈y - x₀⌉, ?_⟩
    have h1 := Int.le_ceil (y - x₀)
    have h2 : ((⌈y - x₀⌉ : ℤ) : ℝ) < x - x₀ := Int.lt_ceil.mp hlt
    rw [abs_le] at hxy ⊢; constructor <;> linarith

/-- **Permutation of residues.** If `u p + v K = 1`, then `i ↦ i p mod K` permutes `{0,…,K-1}`. -/
lemma sum_mul_emod_perm {β : Type*} [AddCommMonoid β] {K : ℕ} (hK : 1 ≤ K) {p u v : ℤ}
    (huv : u * p + v * K = 1) (g : ℤ → β) :
    ∑ i ∈ range K, g ((i : ℤ) * p % K) = ∑ k ∈ range K, g k := by
  have hK0 : (0 : ℤ) < K := by exact_mod_cast hK
  -- `(i p mod K) u ≡ i` and `(k u mod K) p ≡ k` modulo `K`
  have inv1 : ∀ i : ℤ, ((i * p % K) * u) % K = i % K := by
    intro i
    have : (i * p % K) * u ≡ i [ZMOD K] := by
      calc (i * p % K) * u ≡ (i * p) * u [ZMOD K] := (Int.mod_modEq _ _).mul_right _
        _ = i * (u * p + v * K) - i * v * K := by ring
        _ = i - i * v * K := by rw [huv]; ring
        _ ≡ i [ZMOD K] := by
          rw [Int.modEq_iff_dvd]; exact ⟨i * v, by ring⟩
    exact this
  have inv2 : ∀ k : ℤ, ((k * u % K) * p) % K = k % K := by
    intro k
    have : (k * u % K) * p ≡ k [ZMOD K] := by
      calc (k * u % K) * p ≡ (k * u) * p [ZMOD K] := (Int.mod_modEq _ _).mul_right _
        _ = k * (u * p + v * K) - k * v * K := by ring
        _ = k - k * v * K := by rw [huv]; ring
        _ ≡ k [ZMOD K] := by
          rw [Int.modEq_iff_dvd]; exact ⟨k * v, by ring⟩
    exact this
  refine Finset.sum_nbij' (fun i => ((i : ℤ) * p % K).toNat) (fun k => ((k : ℤ) * u % K).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_coe, Finset.mem_range]
    have h1 := Int.emod_nonneg ((i : ℤ) * p) hK0.ne'
    have h2 := Int.emod_lt_of_pos ((i : ℤ) * p) hK0
    omega
  · intro k _
    simp only [Finset.mem_coe, Finset.mem_range]
    have h1 := Int.emod_nonneg ((k : ℤ) * u) hK0.ne'
    have h2 := Int.emod_lt_of_pos ((k : ℤ) * u) hK0
    omega
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    have h1 := Int.emod_nonneg ((i : ℤ) * p) hK0.ne'
    have e := inv1 i
    have hi' : (i : ℤ) % K = i := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)
    rw [Int.toNat_of_nonneg h1, e, hi']
    simp
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    have h1 := Int.emod_nonneg ((k : ℤ) * u) hK0.ne'
    have e := inv2 k
    have hk' : (k : ℤ) % K = k := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hk)
    rw [Int.toNat_of_nonneg h1, e, hk']
    simp
  · intro i _
    have h1 := Int.emod_nonneg ((i : ℤ) * p) hK0.ne'
    rw [Int.toNat_of_nonneg h1]

end CollatzCLT

namespace CollatzCLT

open Real Finset

/-- `q(γ + i p / K) = q(γ + (i p mod K) / K)` by periodicity. -/
lemma PiecewiseLip.eq_emod {q : ℝ → ℂ} {M L x₀ : ℝ} (hq : PiecewiseLip q M L x₀) {K : ℕ}
    (hK : 1 ≤ K) (p : ℤ) (γ : ℝ) (i : ℕ) :
    q (γ + i * ((p : ℝ) / K)) = q (γ + ((((i : ℤ) * p % K : ℤ)) : ℝ) / K) := by
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
  have hdiv := Int.emod_add_mul_ediv ((i : ℤ) * p) K
  have : γ + i * ((p : ℝ) / K) = γ + ((((i : ℤ) * p % K : ℤ)) : ℝ) / K + (((i : ℤ) * p / K : ℤ) : ℝ) * 1 := by
    have hR : (((i : ℤ) * p % K : ℤ) : ℝ) + (K : ℝ) * (((i : ℤ) * p / K : ℤ) : ℝ) = (i : ℝ) * p := by
      exact_mod_cast hdiv
    field_simp
    linarith
  rw [this]; exact (Function.Periodic.int_mul hq.periodic _) _

/-- **Block estimate.** If `u p + v K = 1` and `|θ' - p/K| ≤ 1/(KQ)` with `Q ≥ 2`, then for every `γ`,
`|∑_{i<K} q(γ + iθ') - K ∫₀¹ q| ≤ (L + 2M) + KL/Q + 6M(2K/Q + 1)`. -/
theorem PiecewiseLip.block_bound {q : ℝ → ℂ} {M L x₀ : ℝ} (hq : PiecewiseLip q M L x₀) {K : ℕ}
    (hK : 1 ≤ K) {p u v : ℤ} (huv : u * p + v * K = 1) {Q θ' : ℝ} (hQ : 2 ≤ Q)
    (happrox : |θ' - p / K| ≤ 1 / (K * Q)) (γ : ℝ) :
    ‖∑ i ∈ range K, q (γ + i * θ') - K * ∫ x in (0 : ℝ)..1, q x‖ ≤
      (L + 2 * M) + K * L / Q + 2 * M * (3 * (2 * (1 / Q) * K + 1)) := by
  classical
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hQ0 : 0 < Q := by linarith
  have hL := hq.L_nonneg
  have hM := hq.M_nonneg
  -- grid points `y_i = γ + i p / K`; the grid sum is a permuted `grid_sum`
  have hgrid : ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K)) = ∑ k ∈ range K, q (γ + k / K) := by
    rw [sum_congr rfl fun i _ => hq.eq_emod hK p γ i]
    have := sum_mul_emod_perm hK huv (fun j : ℤ => q (γ + (j : ℝ) / K))
    simpa using this
  -- near-jump indicator on the grid
  set near : ℤ → ℝ := fun j => if ∃ m : ℤ, |(γ - x₀) + (j : ℝ) / K - m| ≤ 1 / Q then 1 else 0
    with hnear
  have hnear_sum : ∑ i ∈ range K, near ((i : ℤ) * p % K) ≤ 3 * (2 * (1 / Q) * K + 1) := by
    rw [sum_mul_emod_perm hK huv near]
    have := card_near_int_le hK (γ - x₀) (r := 1 / Q) (by positivity)
      (by rw [div_le_div_iff₀ hQ0 (by norm_num)]; linarith)
    refine le_trans (le_of_eq ?_) this
    rw [Finset.card_filter]
    push_cast
    apply sum_congr rfl
    intro k _
    simp only [hnear, Int.cast_natCast]
  -- termwise comparison of rotation points and grid points
  have hterm : ∀ i ∈ range K, ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖ ≤
      L / Q + 2 * M * near ((i : ℤ) * p % K) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiK : (i : ℝ) ≤ K := by exact_mod_cast hi.le
    have hdist : |(γ + i * θ') - (γ + i * ((p : ℝ) / K))| ≤ 1 / Q := by
      rw [show γ + i * θ' - (γ + i * ((p : ℝ) / K)) = i * (θ' - p / K) by ring, abs_mul,
        Nat.abs_cast]
      calc (i : ℝ) * |θ' - p / K| ≤ K * (1 / (K * Q)) := by gcongr
        _ = 1 / Q := by field_simp
    have hnn : 0 ≤ near ((i : ℤ) * p % K) := by simp only [hnear]; split_ifs <;> norm_num
    by_cases hc : ⌈(γ + i * θ') - x₀⌉ = ⌈(γ + i * ((p : ℝ) / K)) - x₀⌉
    · calc ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖
          ≤ L * |(γ + i * θ') - (γ + i * ((p : ℝ) / K))| := hq.cell_lip hc
        _ ≤ L * (1 / Q) := by gcongr
        _ ≤ L / Q + 2 * M * near ((i : ℤ) * p % K) := by
            rw [mul_one_div]; nlinarith
    · -- a jump lies between them, so the grid point is near an integer
      obtain ⟨m, hm⟩ := exists_int_near_of_ceil_ne hdist hc
      have hnear1 : near ((i : ℤ) * p % K) = 1 := by
        simp only [hnear]
        rw [if_pos]
        refine ⟨m - ((i : ℤ) * p / K), ?_⟩
        have hdiv := Int.emod_add_mul_ediv ((i : ℤ) * p) K
        have hR : (((i : ℤ) * p % K : ℤ) : ℝ) + (K : ℝ) * (((i : ℤ) * p / K : ℤ) : ℝ) =
            (i : ℝ) * p := by exact_mod_cast hdiv
        have e : (γ - x₀) + (((i : ℤ) * p % K : ℤ) : ℝ) / K - ((m - (i : ℤ) * p / K : ℤ) : ℝ) =
            γ + i * ((p : ℝ) / K) - x₀ - m := by
          push_cast; field_simp; linarith
        rw [e]; exact hm
      rw [hnear1, mul_one]
      calc ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖
          ≤ ‖q (γ + i * θ')‖ + ‖q (γ + i * ((p : ℝ) / K))‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hq.bdd _) (hq.bdd _)
        _ ≤ L / Q + 2 * M := by have : 0 ≤ L / Q := by positivity
                                linarith
  have hsum : ‖∑ i ∈ range K, q (γ + i * θ') - ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K))‖ ≤
      K * L / Q + 2 * M * (3 * (2 * (1 / Q) * K + 1)) := by
    rw [← sum_sub_distrib]
    calc ‖∑ i ∈ range K, (q (γ + i * θ') - q (γ + i * ((p : ℝ) / K)))‖
        ≤ ∑ i ∈ range K, ‖q (γ + i * θ') - q (γ + i * ((p : ℝ) / K))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range K, (L / Q + 2 * M * near ((i : ℤ) * p % K)) := sum_le_sum hterm
      _ = K * L / Q + 2 * M * ∑ i ∈ range K, near ((i : ℤ) * p % K) := by
          rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ K * L / Q + 2 * M * (3 * (2 * (1 / Q) * K + 1)) := by gcongr
  have hg := hq.grid_sum hK γ
  rw [← hgrid] at hg
  calc ‖∑ i ∈ range K, q (γ + i * θ') - K * ∫ x in (0 : ℝ)..1, q x‖
      ≤ ‖∑ i ∈ range K, q (γ + i * θ') - ∑ i ∈ range K, q (γ + i * ((p : ℝ) / K))‖ +
        ‖∑ i ∈ range K, q (γ + i * ((p : ℝ) / K)) - K * ∫ x in (0 : ℝ)..1, q x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K * L / Q + 2 * M * (3 * (2 * (1 / Q) * K + 1))) + (L + 2 * M) := add_le_add hsum hg
    _ = _ := by ring

end CollatzCLT
