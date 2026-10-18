import Mathlib

/-!
# Dyadic bookkeeping for Lemma 6.5 [`lem:sampling`]

Two exact decompositions of a sum over `[1, X]`, and a dominated-convergence lemma.

* `sum_Icc_eq_sum_blocks`: `[1, Z]` is the disjoint union of the dyadic blocks
  `(⌊Z/2^{k+1}⌋, ⌊Z/2^k⌋]`, `k = 0, 1, …`.
* `sum_Icc_two_adic`: writing `n = 2^e u` with `u` odd,
  `∑_{n ≤ X} g(n) = ∑_e ∑_{u odd, u ≤ X/2^e} g(2^e u)`.
* `dyadic_tannery`: if the normalised sum over each dyadic block tends to `ℓ/2^{k+1}`,
  then the normalised sum over `[1, Z]` tends to `ℓ`. This is Tannery's theorem with
  domination `2^{-k}`, and it replaces the truncation arguments (`E₀ → ∞`, `J₀ → ∞`)
  in the proof of Lemma 6.5 [`lem:sampling`].
-/

open Finset Filter Topology

namespace CollatzCLT

/-- Consecutive dyadic blocks telescope. -/
lemma sum_blocks_telescope {M : Type*} [AddCommMonoid M] (g : ℕ → M) (Z K : ℕ) :
    ∑ k ∈ range K, ∑ n ∈ Ioc (Z / 2 ^ (k + 1)) (Z / 2 ^ k), g n = ∑ n ∈ Ioc (Z / 2 ^ K) Z, g n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, add_comm]
    exact sum_Ioc_consecutive g
      (Nat.div_le_div_left (Nat.pow_le_pow_right two_pos (Nat.le_succ K)) (by positivity))
      (Nat.div_le_self _ _)

/-- **Dyadic blocks.** `[1, Z]` is the disjoint union of `(⌊Z/2^{k+1}⌋, ⌊Z/2^k⌋]`, `k ≤ Z`. -/
theorem sum_Icc_eq_sum_blocks {M : Type*} [AddCommMonoid M] (g : ℕ → M) (Z : ℕ) :
    ∑ n ∈ Icc 1 Z, g n = ∑ k ∈ range (Z + 1), ∑ n ∈ Ioc (Z / 2 ^ (k + 1)) (Z / 2 ^ k), g n := by
  rw [sum_blocks_telescope]
  have h0 : Z / 2 ^ (Z + 1) = 0 :=
    Nat.div_eq_of_lt ((Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self Z)))
  rw [h0]
  rfl

/-- Blocks beyond `k = Z` are empty. -/
lemma block_eq_empty {Z k : ℕ} (hk : Z + 1 ≤ k) : Ioc (Z / 2 ^ (k + 1)) (Z / 2 ^ k) = ∅ := by
  have h1 : Z / 2 ^ k = 0 :=
    Nat.div_eq_of_lt ((Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right two_pos (by omega)))
  rw [h1]; simp

/-- Splitting a sum over `[1, Y]` into odd terms and even terms `2m`, `m ≤ Y/2`. -/
lemma sum_Icc_split_even {M : Type*} [AddCommMonoid M] (h : ℕ → M) (Y : ℕ) :
    ∑ m ∈ Icc 1 Y, h m = ∑ m ∈ (Icc 1 Y).filter Odd, h m + ∑ m ∈ Icc 1 (Y / 2), h (2 * m) := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 Y) Odd]
  congr 1
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by simpa using hab
  rw [show (∑ m ∈ Icc 1 (Y / 2), h (2 * m)) = ∑ x ∈ (Icc 1 (Y / 2)).map ⟨_, hinj⟩, h x from
    by rw [sum_map]; rfl]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.not_odd_iff_even, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
    exact ⟨m, ⟨by omega, by omega⟩, by ring⟩
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, ⟨m, by ring⟩⟩

/-- **Two-adic decomposition.** `∑_{n ≤ X} g(n) = ∑_{e<E} ∑_{u odd ≤ X/2^e} g(2^e u)
+ ∑_{m ≤ X/2^E} g(2^E m)`. -/
lemma sum_Icc_two_adic_aux {M : Type*} [AddCommMonoid M] (g : ℕ → M) (X : ℕ) :
    ∀ E : ℕ, ∑ n ∈ Icc 1 X, g n = ∑ e ∈ range E, ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, g (2 ^ e * u)
      + ∑ m ∈ Icc 1 (X / 2 ^ E), g (2 ^ E * m) := by
  intro E
  induction E with
  | zero => simp
  | succ E ih =>
    rw [ih, sum_range_succ, add_assoc, sum_Icc_split_even (fun m => g (2 ^ E * m)),
      Nat.div_div_eq_div_mul, ← pow_succ]
    congr 3
    ext m
    ring_nf

/-- **Two-adic decomposition**, complete form. -/
theorem sum_Icc_two_adic {M : Type*} [AddCommMonoid M] (g : ℕ → M) (X : ℕ) :
    ∑ n ∈ Icc 1 X, g n = ∑ e ∈ range (X + 1), ∑ u ∈ (Icc 1 (X / 2 ^ e)).filter Odd, g (2 ^ e * u) := by
  rw [sum_Icc_two_adic_aux g X (X + 1)]
  have h0 : X / 2 ^ (X + 1) = 0 :=
    Nat.div_eq_of_lt ((Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self X)))
  simp [h0]

/-- **Dyadic Tannery lemma.** Let `f i` be `1`-bounded and let the size `Z i → ∞`. If, for each
fixed `k`, the sum over the `k`-th dyadic block of `[1, Z i]`, divided by `Z i`, tends to
`ℓ / 2^{k+1}`, then the average over `[1, Z i]` tends to `ℓ`. -/
theorem dyadic_tannery {ι : Type*} {L : Filter ι} {Z : ι → ℕ} {f : ι → ℕ → ℂ}
    (hf : ∀ i n, ‖f i n‖ ≤ 1) {ℓ : ℂ}
    (hblock : ∀ k : ℕ, Tendsto (fun i => ((Z i : ℂ))⁻¹ *
      ∑ n ∈ Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k), f i n) L (𝓝 (ℓ / 2 ^ (k + 1)))) :
    Tendsto (fun i => ((Z i : ℂ))⁻¹ * ∑ n ∈ Icc 1 (Z i), f i n) L (𝓝 ℓ) := by
  set F : ι → ℕ → ℂ := fun i k => ((Z i : ℂ))⁻¹ * ∑ n ∈ Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k), f i n
    with hF
  -- the average is the (finite) sum of the block terms
  have hsum : ∀ i, ((Z i : ℂ))⁻¹ * ∑ n ∈ Icc 1 (Z i), f i n = ∑' k, F i k := by
    intro i
    rw [tsum_eq_sum (s := range (Z i + 1)), sum_Icc_eq_sum_blocks, mul_sum]
    intro k hk
    simp only [mem_range, not_lt] at hk
    simp [hF, block_eq_empty hk]
  -- domination by `2^{-k}`
  have hbound : ∀ i k, ‖F i k‖ ≤ (1 / 2 : ℝ) ^ k := by
    intro i k
    rcases Nat.eq_zero_or_pos (Z i) with hz | hz
    · simp [hF, hz]
    have hcard : ((Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k)).card : ℝ) ≤ (Z i : ℝ) / 2 ^ k := by
      rw [Nat.card_Ioc]
      calc ((Z i / 2 ^ k - Z i / 2 ^ (k + 1) : ℕ) : ℝ) ≤ ((Z i / 2 ^ k : ℕ) : ℝ) := by
            exact_mod_cast Nat.sub_le _ _
        _ ≤ (Z i : ℝ) / 2 ^ k := by
            rw [le_div_iff₀ (by positivity)]
            exact_mod_cast Nat.div_mul_le_self _ _
    calc ‖F i k‖ ≤ ((Z i : ℝ))⁻¹ * ∑ n ∈ Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k), ‖f i n‖ := by
          rw [hF]; simp only [norm_mul, norm_inv, Complex.norm_natCast]
          gcongr; exact norm_sum_le _ _
      _ ≤ ((Z i : ℝ))⁻¹ * (Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k)).card := by
          gcongr
          calc ∑ n ∈ Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k), ‖f i n‖
              ≤ ∑ n ∈ Ioc (Z i / 2 ^ (k + 1)) (Z i / 2 ^ k), (1 : ℝ) := sum_le_sum (fun n _ => hf i n)
            _ = _ := by simp
      _ ≤ ((Z i : ℝ))⁻¹ * ((Z i : ℝ) / 2 ^ k) := by gcongr
      _ = (1 / 2 : ℝ) ^ k := by
          have : (Z i : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
          rw [div_pow, one_pow]
          field_simp
  have hsummable : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hT := tendsto_tsum_of_dominated_convergence hsummable hblock
    (Eventually.of_forall (hbound ·))
  -- `∑ ℓ / 2^{k+1} = ℓ`
  have hgeom : ∑' k : ℕ, ℓ / 2 ^ (k + 1) = ℓ := by
    have h2 : ∑' k : ℕ, ((1 : ℂ) / 2) ^ k = 2 := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num)]; norm_num
    calc ∑' k : ℕ, ℓ / 2 ^ (k + 1) = ∑' k : ℕ, (ℓ / 2) * ((1 : ℂ) / 2) ^ k := by
          congr 1; ext k; rw [div_pow, one_pow, pow_succ]; field_simp
      _ = ℓ := by rw [tsum_mul_left, h2]; ring
  rw [hgeom] at hT
  refine hT.congr' (Eventually.of_forall fun i => ?_)
  exact (hsum i).symm

end CollatzCLT
