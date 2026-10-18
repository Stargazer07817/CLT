import LeanClt.Mixing.Fourier
import LeanClt.Transfer.Geom
import LeanClt.Transfer.Identity

/-!
# §3.1: the counter twist preserves Tao's majorant

* `conv_lawS`: convolution in the counter with the law of `S_t` preserves `ℓ¹` mass.
* `XmodN_append`: `X̃(u ++ v) = X̃(u) + 3^{|u|} 2^{-Σu} X̃(v)` (target-outward order).
* `condChar N ζ a = ∏_{j<⌊r/2⌋} f_ζ(3^{2j} 2^{-B_{j+1}}, b_{j+1})`: Tao's conditional character,
  i.e. `E[χ_ζ(X̃) | 𝓗]` at the pair sums of `a`; `majorantAt ζ a = ‖condChar n ζ a‖`.
* `sum_chiZ_eq_sum_condChar`: for words of even length and fixed total `s`,
  `∑_a χ_ζ(X̃(a)) = ∑_a condChar(a)` — the tower property at fixed counter value, proved by
  appending one pair at a time. `norm_sum_chiZ_le` is the resulting bound for every length.
* **Lemma 3.2** (`lem:weighted`), counter-resolved form `weighted_resolved`:
  `∑_s |E[1{S_r = s} χ_ζ(X_r)]| ≤ E ∏_j |f_ζ(…)|` for every `ζ`; with Tao's majorant bound
  (`weighted_bound`) this is `≤ C_B r^{-B}` for `3 ∤ ζ`. The paper's twisted form (3.3,
  `eq:twisted`) follows by the triangle inequality (`twisted_bound`).
* **Corollary 3.3** (`cor:conductor`), counter-resolved form `conductor_resolved` /
  `conductor_bound`: a character of `ℤ/3^Nℤ` of conductor `3^r` sees only the first `r` letters,
  and the remaining `N - r` letters only convolve the counter.

The counter-resolved bound is (3.2, `eq:weighted`) for the weights `G = g(S_n)`, `|g| ≤ 1`, that are
functions of the counter: `∑_s |E[1{S_n = s} χ]| = sup_{|g| ≤ 1} |E[g(S_n) χ]|`. That is all §3
uses; (3.2) for a general `𝓗_n`-measurable `G` is not formalized. It is stronger than (3.3).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-! ## Convolution in the counter -/

/-- **Convolution with the law of `S_t` preserves the total** of an absolutely summable
sequence (`∑_s ∑_{s₁ ≤ s} G(s₁) P(S_t = s - s₁) = ∑ G`). -/
lemma conv_lawS {G : ℕ → ℝ} (hG : Summable G) (t : ℕ) :
    Summable (fun s => ∑ s1 ∈ range (s + 1), G s1 * lawS t (s - s1)) ∧
      ∑' s, ∑ s1 ∈ range (s + 1), G s1 * lawS t (s - s1) = ∑' s, G s := by
  have hGn : Summable fun s => ‖G s‖ := by simp_rw [Real.norm_eq_abs]; exact hG.abs
  have hLn : Summable fun s => ‖lawS t s‖ := by
    simp_rw [Real.norm_eq_abs]; exact (summable_lawS t).abs
  refine ⟨(summable_norm_sum_mul_range_of_summable_norm hGn hLn).of_norm, ?_⟩
  rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hGn hLn, tsum_lawS, mul_one]

lemma norm_half_pow_mul (s : ℕ) (z : ℂ) : ‖(1 / 2 : ℂ) ^ s * z‖ = (1 / 2 : ℝ) ^ s * ‖z‖ := by
  rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_ofNat]

/-! ## Offsets of concatenated words -/

lemma psum_append_left {p t : ℕ} (u : Fin p → ℕ) (v : Fin t → ℕ) (j : Fin p) :
    psum (Fin.append u v) (Fin.castAdd t j) = psum u j := by
  unfold psum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h2 : ∑ i : Fin t, (if Fin.natAdd p i ≤ Fin.castAdd t j then v i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg (by
      rw [Fin.le_iff_val_le_val, Fin.val_natAdd, Fin.val_castAdd]; have := j.isLt; omega)
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.le_iff_val_le_val, Fin.val_castAdd]

lemma psum_append_right {p t : ℕ} (u : Fin p → ℕ) (v : Fin t → ℕ) (j : Fin t) :
    psum (Fin.append u v) (Fin.natAdd p j) = (∑ i, u i) + psum v j := by
  unfold psum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => if_pos ?_
    rw [Fin.le_iff_val_le_val, Fin.val_natAdd, Fin.val_castAdd]; have := i.isLt; omega
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.natAdd_le_natAdd_iff]

/-- **Concatenation:** `X̃(u ++ v) = X̃(u) + 3^{|u|} 2^{-Σu} X̃(v)`, at any modulus. -/
theorem XmodN_append (N : ℕ) {p t : ℕ} (u : Fin p → ℕ) (v : Fin t → ℕ) :
    XmodN N (Fin.append u v) = XmodN N u + 3 ^ p * half N ^ (∑ i, u i) * XmodN N v := by
  unfold XmodN
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [psum_append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [psum_append_right, Fin.val_natAdd, pow_add, pow_add]; ring

lemma Xmod_eq_XmodN {n : ℕ} (a : Fin n → ℕ) : Xmod a = XmodN n a := rfl

/-- A pair `(v₀, v₁)` contributes `2^{-(v₀+v₁)} (2^{v₁} + 3)`. -/
lemma XmodN_two (N : ℕ) (v : Fin 2 → ℕ) :
    XmodN N v = half N ^ (v 0 + v 1) * (2 ^ (v 1) + 3) := by
  have h1 : psum v 0 = v 0 := by simp [psum]
  have h2 : psum v 1 = v 0 + v 1 := by simp [psum, Fin.sum_univ_two]
  unfold XmodN
  rw [Fin.sum_univ_two, h1, h2]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, one_mul, pow_one]
  rw [pow_add]
  have := two_pow_mul_half_pow N (v 1)
  linear_combination (-half N ^ v 0) * this

/-- Reduction of an offset to a smaller modulus. -/
lemma cast_XmodN {r N : ℕ} (h : r ≤ N) {p : ℕ} (v : Fin p → ℕ) :
    (ZMod.cast (XmodN N v) : ZMod (3 ^ r)) = XmodN r v := by
  rw [← ZMod.castHom_apply (h := pow_dvd_pow 3 h)]
  unfold XmodN
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_pow, cast_half h, map_ofNat]

/-! ## Words of length two -/

lemma sum_words_two (b : ℕ) {β : Type*} [AddCommMonoid β] (F : ℕ → β) :
    ∑ v ∈ words 2 b, F (v 1) = ∑ a ∈ Icc 1 (b - 1), F a := by
  refine Finset.sum_nbij' (fun v => v 1) (fun a => ![b - a, a]) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_words, Fin.sum_univ_two] at hv
    have := hv.2 0; have := hv.2 1
    simp only [mem_Icc]; omega
  · intro a ha
    simp only [mem_Icc] at ha
    rw [mem_words, Fin.sum_univ_two]
    refine ⟨by simp; omega, fun i => ?_⟩
    fin_cases i <;> simp <;> omega
  · intro v hv
    rw [mem_words, Fin.sum_univ_two] at hv
    funext i
    fin_cases i
    · simp; omega
    · simp
  · intro a _; simp
  · intro v _; rfl

lemma card_words_two (b : ℕ) : (words 2 b).card = b - 1 := by
  rw [Finset.card_eq_sum_ones, sum_words_two b (fun _ => 1), ← Finset.card_eq_sum_ones,
    Nat.card_Icc]
  omega

/-! ## Tao's conditional character -/

lemma norm_fTao_le_one {N : ℕ} (ξ x : ZMod (3 ^ N)) (b : ℕ) : ‖fTao ξ x b‖ ≤ 1 := by
  unfold fTao
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (b - 1) with hb | hb
  · rw [hb]; simp
  · have hs : ‖∑ a ∈ Icc 1 (b - 1), chiZ ξ (x * (2 ^ a + 3))‖ ≤ ((b - 1 : ℕ) : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      simp [norm_chiZ]
    have hb' : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by exact_mod_cast hb
    calc ((b - 1 : ℕ) : ℝ)⁻¹ * ‖∑ a ∈ Icc 1 (b - 1), chiZ ξ (x * (2 ^ a + 3))‖
        ≤ ((b - 1 : ℕ) : ℝ)⁻¹ * ((b - 1 : ℕ) : ℝ) := by gcongr
      _ = 1 := inv_mul_cancel₀ hb'.ne'

/-- The `(j+1)`-th factor `f_ζ(3^{2j} 2^{-B_{j+1}}, b_{j+1})` of Tao's conditional character. -/
def condFactor (N : ℕ) (ζ : ZMod (3 ^ N)) {r : ℕ} (a : Fin r → ℕ) (j : ℕ) : ℂ :=
  fTao ζ ((3 : ZMod (3 ^ N)) ^ (2 * j) * half N ^ wsum (ext a) (2 * j + 2)) (pairSum a j)

/-- Tao's conditional character `E[χ_ζ(X̃_r) | 𝓗_r] = ω ∏_{j<⌊r/2⌋} f_ζ(3^{2j} 2^{-B_{j+1}}, b_{j+1})`
(without the unimodular factor `ω` of the unpaired last letter), at modulus `3^N`. -/
def condChar (N : ℕ) (ζ : ZMod (3 ^ N)) {r : ℕ} (a : Fin r → ℕ) : ℂ :=
  ∏ j ∈ range (r / 2), condFactor N ζ a j

lemma majorantAt_eq {n : ℕ} (ζ : ZMod (3 ^ n)) (a : Fin n → ℕ) :
    majorantAt ζ a = ‖condChar n ζ a‖ := by
  rw [condChar, norm_prod]; rfl

lemma majorantAt_nonneg {n : ℕ} (ζ : ZMod (3 ^ n)) (a : Fin n → ℕ) : 0 ≤ majorantAt ζ a := by
  rw [majorantAt_eq]; exact norm_nonneg _

lemma majorantAt_le_one {n : ℕ} (ζ : ZMod (3 ^ n)) (a : Fin n → ℕ) : majorantAt ζ a ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_fTao_le_one _ _ _)

lemma ext_append_right {m t : ℕ} (a1 : Fin m → ℕ) (a2 : Fin t → ℕ) {i : ℕ} (hi : i < t) :
    ext (Fin.append a1 a2) (m + i) = ext a2 i := by
  simp only [ext, hi, ↓reduceDIte, show m + i < m + t by omega]
  exact Fin.append_right a1 a2 ⟨i, hi⟩

lemma condFactor_append {N : ℕ} (ζ : ZMod (3 ^ N)) {p t : ℕ} (u : Fin p → ℕ) (v : Fin t → ℕ)
    {j : ℕ} (hj : 2 * j + 2 ≤ p) : condFactor N ζ (Fin.append u v) j = condFactor N ζ u j := by
  unfold condFactor pairSum
  rw [wsum_congr fun i hi => ext_append_left u v (by omega), ext_append_left u v (by omega),
    ext_append_left u v (by omega)]

lemma condChar_append_two (N : ℕ) (ζ : ZMod (3 ^ N)) {k : ℕ} (u : Fin (2 * k) → ℕ)
    (v : Fin 2 → ℕ) :
    condChar N ζ (Fin.append u v) = condChar N ζ u *
      fTao ζ ((3 : ZMod (3 ^ N)) ^ (2 * k) * half N ^ ((∑ i, u i) + (v 0 + v 1))) (v 0 + v 1) := by
  unfold condChar
  rw [show (2 * k + 2) / 2 = k + 1 by omega, show 2 * k / 2 = k by omega, prod_range_succ]
  congr 1
  · exact Finset.prod_congr rfl fun j hj =>
      condFactor_append ζ u v (by have := mem_range.mp hj; omega)
  · have hw : wsum (ext (Fin.append u v)) (2 * k + 2) = (∑ i, u i) + (v 0 + v 1) := by
      rw [wsum_ext, Fin.sum_univ_add, Fin.sum_univ_two]
      simp only [Fin.append_left, Fin.append_right]
    have h0 : ext (Fin.append u v) (2 * k) = v 0 := by
      have := ext_append_right u v (i := 0) (by norm_num); simpa [ext] using this
    have h1 : ext (Fin.append u v) (2 * k + 1) = v 1 := by
      have := ext_append_right u v (i := 1) (by norm_num); simpa [ext] using this
    unfold condFactor pairSum
    rw [hw, h0, h1]

lemma condChar_append_one (N : ℕ) (ζ : ZMod (3 ^ N)) {k : ℕ} (u : Fin (2 * k) → ℕ)
    (v : Fin 1 → ℕ) : condChar N ζ (Fin.append u v) = condChar N ζ u := by
  unfold condChar
  rw [show (2 * k + 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
  exact Finset.prod_congr rfl fun j hj =>
    condFactor_append ζ u v (by have := mem_range.mp hj; omega)

/-- The inner average over the split of one pair. -/
lemma sum_words_two_chiZ (N : ℕ) (ζ x : ZMod (3 ^ N)) (b : ℕ) :
    ∑ v ∈ words 2 b, chiZ ζ (x * XmodN N v) = ∑ v ∈ words 2 b, fTao ζ (x * half N ^ b) b := by
  have h1 : ∑ v ∈ words 2 b, chiZ ζ (x * XmodN N v) =
      ∑ v ∈ words 2 b, chiZ ζ (x * half N ^ b * (2 ^ (v 1) + 3)) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [mem_words, Fin.sum_univ_two] at hv
    rw [XmodN_two, hv.1, mul_assoc]
  have h2 := sum_words_two b (fun a => chiZ ζ (x * half N ^ b * (2 ^ a + 3)))
  rw [h1, h2, Finset.sum_const, card_words_two, nsmul_eq_mul]
  unfold fTao
  rcases Nat.eq_zero_or_pos (b - 1) with hb | hb
  · rw [hb]; simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hb.ne'), one_mul]

/-- **The tower property at a fixed counter value** (even length): averaging the character
over the splits of each pair gives Tao's conditional character. -/
theorem sum_chiZ_eq_sum_condChar (N : ℕ) (ζ : ZMod (3 ^ N)) (k : ℕ) : ∀ s : ℕ,
    ∑ a ∈ words (2 * k) s, chiZ ζ (XmodN N a) = ∑ a ∈ words (2 * k) s, condChar N ζ a := by
  induction k with
  | zero =>
    intro s
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [XmodN, condChar, chiZ_zero]
  | succ k ih =>
    intro s
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, sum_words_append (2 * k) 2 s,
      sum_words_append (2 * k) 2 s]
    refine Finset.sum_congr rfl fun s1 _ => ?_
    have hL : ∀ u ∈ words (2 * k) s1,
        ∑ v ∈ words 2 (s - s1), chiZ ζ (XmodN N (Fin.append u v)) =
          chiZ ζ (XmodN N u) * ∑ v ∈ words 2 (s - s1),
            fTao ζ ((3 : ZMod (3 ^ N)) ^ (2 * k) * half N ^ s1 * half N ^ (s - s1)) (s - s1) := by
      intro u hu
      rw [← sum_words_two_chiZ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [XmodN_append, chiZ_add, (mem_words.mp hu).1]
    have hR : ∀ u ∈ words (2 * k) s1,
        ∑ v ∈ words 2 (s - s1), condChar N ζ (Fin.append u v) =
          condChar N ζ u * ∑ v ∈ words 2 (s - s1),
            fTao ζ ((3 : ZMod (3 ^ N)) ^ (2 * k) * half N ^ s1 * half N ^ (s - s1)) (s - s1) := by
      intro u hu
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hv' := (mem_words.mp hv).1
      rw [Fin.sum_univ_two] at hv'
      rw [condChar_append_two, (mem_words.mp hu).1, hv', pow_add, ← mul_assoc]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.sum_mul, ← Finset.sum_mul,
      ih s1]

/-- **The majorant bound at a fixed counter value**, for words of any length. -/
theorem norm_sum_chiZ_le (N : ℕ) (ζ : ZMod (3 ^ N)) (r s : ℕ) :
    ‖∑ a ∈ words r s, chiZ ζ (XmodN N a)‖ ≤ ∑ a ∈ words r s, ‖condChar N ζ a‖ := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [sum_chiZ_eq_sum_condChar]; exact norm_sum_le _ _
  · rw [sum_words_append (2 * k) 1 s, sum_words_append (2 * k) 1 s]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s1 _ => ?_)
    have hL : ∑ u ∈ words (2 * k) s1, ∑ v ∈ words 1 (s - s1), chiZ ζ (XmodN N (Fin.append u v)) =
        (∑ u ∈ words (2 * k) s1, condChar N ζ u) *
          ∑ v ∈ words 1 (s - s1), chiZ ζ ((3 : ZMod (3 ^ N)) ^ (2 * k) * half N ^ s1 * XmodN N v) := by
      rw [← sum_chiZ_eq_sum_condChar, Finset.sum_mul]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [XmodN_append, chiZ_add, (mem_words.mp hu).1]
    have hR : ∑ u ∈ words (2 * k) s1, ∑ v ∈ words 1 (s - s1), ‖condChar N ζ (Fin.append u v)‖ =
        (∑ u ∈ words (2 * k) s1, ‖condChar N ζ u‖) * ((words 1 (s - s1)).card : ℝ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp_rw [condChar_append_one]
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hL, hR, norm_mul]
    gcongr
    · exact norm_sum_le _ _
    · refine (norm_sum_le _ _).trans ?_
      simp [norm_chiZ]

/-! ## Lemma 3.2, counter-resolved -/

lemma majorant_term_le (r : ℕ) (ζ : ZMod (3 ^ r)) (s : ℕ) :
    ∑ a ∈ words r s, (1 / 2 : ℝ) ^ s * majorantAt ζ a ≤ lawS r s := by
  rw [← sum_words_half]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_of_le_one_right (by positivity) (majorantAt_le_one ζ a)

lemma summable_majorant (r : ℕ) (ζ : ZMod (3 ^ r)) :
    Summable (fun s => ∑ a ∈ words r s, (1 / 2 : ℝ) ^ s * majorantAt ζ a) :=
  Summable.of_nonneg_of_le
    (fun s => Finset.sum_nonneg fun a _ => mul_nonneg (by positivity) (majorantAt_nonneg ζ a))
    (majorant_term_le r ζ) (summable_lawS r)

/-- **Lemma 3.2 (weighted Fourier bound), counter-resolved form:**
`∑_s |E[1{S_r = s} χ_ζ(X_r)]| ≤ E ∏_j |f_ζ(3^{2j-2} 2^{-B_j}, b_j)|`, for every `ζ`. -/
theorem weighted_resolved (r : ℕ) (ζ : ZMod (3 ^ r)) :
    Summable (fun s => ‖(1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a)‖) ∧
      ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a)‖ ≤ taoMajorant r ζ := by
  have hterm : ∀ s, ‖(1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a)‖ ≤
      ∑ a ∈ words r s, (1 / 2 : ℝ) ^ s * majorantAt ζ a := by
    intro s
    rw [norm_half_pow_mul, ← Finset.mul_sum]
    gcongr
    simp_rw [majorantAt_eq, Xmod_eq_XmodN]
    exact norm_sum_chiZ_le r ζ r s
  have hL := Summable.of_nonneg_of_le (fun s => norm_nonneg _) hterm (summable_majorant r ζ)
  exact ⟨hL, Summable.tsum_le_tsum hterm hL (summable_majorant r ζ)⟩

/-- **Lemma 3.2 with Tao's majorant bound**: `∑_s |E[1{S_r = s} χ_ζ(X_r)]| ≤ C_B r^{-B}` for
`3 ∤ ζ`. -/
theorem weighted_bound (hTM : TaoMajorant) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ r : ℕ, 1 ≤ r → ∀ ζ : ZMod (3 ^ r), ¬ 3 ∣ ζ.val →
      ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a)‖ ≤ C * (r : ℝ) ^ (-B) := by
  obtain ⟨C, hC⟩ := hTM B hB
  exact ⟨C, fun r hr ζ hζ => (weighted_resolved r ζ).2.trans (hC r hr ζ hζ)⟩

/-- **The twisted bound (3.3, `eq:twisted`)**: `sup_t |E[e^{itS_r} χ_ζ(X_r)]| ≤ C_B r^{-B}`. -/
theorem twisted_bound (hTM : TaoMajorant) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ r : ℕ, 1 ≤ r → ∀ ζ : ZMod (3 ^ r), ¬ 3 ∣ ζ.val → ∀ t : ℝ,
      ‖∑' s : ℕ, cexp (((t * s : ℝ) : ℂ) * I) *
        ((1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a))‖ ≤ C * (r : ℝ) ^ (-B) := by
  obtain ⟨C, hC⟩ := weighted_bound hTM hB
  refine ⟨C, fun r hr ζ hζ t => ?_⟩
  have hnorm : ∀ s : ℕ, ‖cexp (((t * s : ℝ) : ℂ) * I) *
      ((1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a))‖ =
      ‖(1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a)‖ := by
    intro s; rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hs : Summable fun s : ℕ => ‖cexp (((t * s : ℝ) : ℂ) * I) *
      ((1 / 2 : ℂ) ^ s * ∑ a ∈ words r s, chiZ ζ (Xmod a))‖ := by
    simp_rw [hnorm]; exact (weighted_resolved r ζ).1
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  simp_rw [hnorm]
  exact hC r hr ζ hζ

/-! ## Corollary 3.3, counter-resolved -/

lemma prefixOf_append {r t : ℕ} (u : Fin r → ℕ) (w : Fin t → ℕ) :
    prefixOf (Nat.le_add_right r t) (Fin.append u w) = u := by
  funext i; exact Fin.append_left u w i

/-- **The tail only convolves the counter.** For any function `F` of the first `r` letters,
`∑_s |E[1{S_{r+t} = s} F(a₁…a_r)]| ≤ ∑_s |E[1{S_r = s} F(a₁…a_r)]|`. -/
theorem conductor_resolved (r t : ℕ) (F : (Fin r → ℕ) → ℂ)
    (hF : Summable fun s => ‖(1 / 2 : ℂ) ^ s * ∑ u ∈ words r s, F u‖) :
    Summable (fun s => ‖(1 / 2 : ℂ) ^ s *
        ∑ v ∈ words (r + t) s, F (prefixOf (Nat.le_add_right r t) v)‖) ∧
      ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ v ∈ words (r + t) s, F (prefixOf (Nat.le_add_right r t) v)‖ ≤
        ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ u ∈ words r s, F u‖ := by
  set G : ℕ → ℝ := fun s => ‖(1 / 2 : ℂ) ^ s * ∑ u ∈ words r s, F u‖ with hGdef
  have hsplit : ∀ s, (1 / 2 : ℂ) ^ s *
      ∑ v ∈ words (r + t) s, F (prefixOf (Nat.le_add_right r t) v) =
      ∑ s1 ∈ range (s + 1), ((1 / 2 : ℂ) ^ s1 * ∑ u ∈ words r s1, F u) * (lawS t (s - s1) : ℂ) := by
    intro s
    rw [sum_words_append r t s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s1 hs1 => ?_
    have hs1 := mem_range.mp hs1
    simp_rw [prefixOf_append]
    have hw : ((words t (s - s1)).card : ℂ) * (1 / 2 : ℂ) ^ (s - s1) = (lawS t (s - s1) : ℂ) := by
      rw [← sum_words_half, Finset.sum_const, nsmul_eq_mul]; push_cast; ring
    have hc : ∑ u ∈ words r s1, ∑ _w ∈ words t (s - s1), F u =
        (∑ u ∈ words r s1, F u) * ((words t (s - s1)).card : ℂ) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hc, ← hw, show (1 / 2 : ℂ) ^ s = (1 / 2) ^ s1 * (1 / 2) ^ (s - s1) by
      rw [← pow_add]; congr 1; omega]
    ring
  have hle : ∀ s, ‖(1 / 2 : ℂ) ^ s *
      ∑ v ∈ words (r + t) s, F (prefixOf (Nat.le_add_right r t) v)‖ ≤
      ∑ s1 ∈ range (s + 1), G s1 * lawS t (s - s1) := by
    intro s
    rw [hsplit]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s1 _ => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lawS_nonneg _ _)]
  obtain ⟨hcs, hct⟩ := conv_lawS hF t
  have hL := Summable.of_nonneg_of_le (fun s => norm_nonneg _) hle hcs
  refine ⟨hL, ?_⟩
  calc _ ≤ ∑' s, ∑ s1 ∈ range (s + 1), G s1 * lawS t (s - s1) :=
        Summable.tsum_le_tsum hle hL hcs
    _ = _ := hct

/-- Reduction of `X̃_N` modulo `3^r` sees only the first `r` letters. -/
lemma cast_Xmod_prefix {r N : ℕ} (h : r ≤ N) (v : Fin N → ℕ) :
    (ZMod.cast (Xmod v) : ZMod (3 ^ r)) = Xmod (prefixOf h v) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  have hv : v = Fin.append (prefixOf h v) (fun i => v (Fin.natAdd r i)) :=
    (Fin.append_castAdd_natAdd (f := v)).symm
  conv_lhs => rw [hv]
  have := cast_Xmod_append (prefixOf h v) (fun i => v (Fin.natAdd r i))
  rwa [ZMod.castHom_apply] at this

/-- **Corollary 3.3 (reduction to the conductor), counter-resolved form.** A character
`χ(x) = χ_ζ(x mod 3^r)` of `ℤ/3^Nℤ` with `3 ∤ ζ` (conductor `3^r`) satisfies
`∑_s |E[1{S_N = s} χ(X_N)]| ≤ C_B r^{-B}`. -/
theorem conductor_bound (hTM : TaoMajorant) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ r N : ℕ, 1 ≤ r → r ≤ N → ∀ ζ : ZMod (3 ^ r), ¬ 3 ∣ ζ.val →
      Summable (fun s => ‖(1 / 2 : ℂ) ^ s *
          ∑ v ∈ words N s, chiZ ζ (ZMod.cast (Xmod v) : ZMod (3 ^ r))‖) ∧
      ∑' s, ‖(1 / 2 : ℂ) ^ s * ∑ v ∈ words N s, chiZ ζ (ZMod.cast (Xmod v) : ZMod (3 ^ r))‖ ≤
        C * (r : ℝ) ^ (-B) := by
  obtain ⟨C, hC⟩ := weighted_bound hTM hB
  refine ⟨C, fun r N hr hrN ζ hζ => ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrN
  have e : ∀ s, ∑ v ∈ words (r + t) s, chiZ ζ (ZMod.cast (Xmod v) : ZMod (3 ^ r)) =
      ∑ v ∈ words (r + t) s, chiZ ζ (Xmod (prefixOf (Nat.le_add_right r t) v)) :=
    fun s => Finset.sum_congr rfl fun v _ => by rw [cast_Xmod_prefix]
  simp_rw [e]
  obtain ⟨h1, h2⟩ := conductor_resolved r t (fun u => chiZ ζ (Xmod u)) (weighted_resolved r ζ).1
  exact ⟨h1, h2.trans (hC r hr ζ hζ)⟩

end CollatzCLT
