import LeanClt.Transfer.FirstPassage
import LeanClt.Transfer.HarmonicAux
import LeanClt.Transfer.Typical

/-!
# Proposition 5.5: the harmonic bound

For `E ⊆ 𝓜_x`, `r + m ≤ n₀` and a residue `z mod 3^r`,
`H_r(z) = 3^r ∑_{M ∈ E, M ≡ z (3^r)} 1/M ≤ 5`.

Proof, following the paper: split `E` according to the valuation word `b` of the `m` steps that
take `M` below `x`, with total `B` and last letter `b_m`.

* `Mbounds`: the crossing condition `U^{m-1}(M) > x ≥ U^m(M)` and the affine formula give
  `(3/2) 2^{B - b_m} x / 3^m ≤ M ≤ 2^B x / 3^m` and `M ≥ (3/8) 2^B / 3^m`.
* The fiber of a word is one class mod `2^{B+1}` (`prefix_iff_modEq`); with the class mod `3^r` it
  is a progression of modulus `Q = 2^{B+1} 3^r`, and `sum_inv_spaced_le` applies.
* Summation over words uses `E[a_m] = 2` and `∑_b 2^{-B/2} ≤ (1+√2)^m`.
-/

open Real Finset

noncomputable section

namespace CollatzCLT

/-- The affine formula (2.1), cast to `ℝ`. -/
lemma U_iterate_affine_real (M j : ℕ) :
    (U^[j] M : ℝ) = 3 ^ j / 2 ^ wsum (vword M) j * M + ((offset (vword M) j : ℚ) : ℝ) := by
  have := congrArg (fun q : ℚ => (q : ℝ)) (U_iterate_affine M j)
  push_cast at this
  exact this

/-- **The bounds (5.9, `eq:Mbounds`)** for a point `M` crossing below `x` at step `k+1`. -/
theorem Mbounds {x : ℝ} {k M : ℕ} (hM : Odd M) (hx : 2 * (3 / 2 : ℝ) ^ k ≤ x)
    (hup : (U^[k + 1] M : ℝ) ≤ x) (hlow : x < (U^[k] M : ℝ)) :
    (M : ℝ) ≤ 2 ^ wsum (vword M) (k + 1) * x / 3 ^ (k + 1) ∧
      3 / 2 * 2 ^ wsum (vword M) k * x / 3 ^ (k + 1) ≤ M ∧
      (3 / 8 : ℝ) * 2 ^ wsum (vword M) (k + 1) / 3 ^ (k + 1) ≤ M := by
  have ha : ∀ i, 1 ≤ vword M i := vword_pos hM
  have hw : wsum (vword M) (k + 1) = wsum (vword M) k + vword M k := Finset.sum_range_succ _ _
  set B' := wsum (vword M) k
  set b := vword M k
  have hF0 : (0 : ℝ) ≤ ((offset (vword M) (k + 1) : ℚ) : ℝ) := by
    exact_mod_cast offset_nonneg _ _
  have hFk0 : (0 : ℝ) ≤ ((offset (vword M) k : ℚ) : ℝ) := by
    exact_mod_cast offset_nonneg _ _
  have hFk : ((offset (vword M) k : ℚ) : ℝ) ≤ (3 / 2 : ℝ) ^ k - 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (offset_le (vword M) ha k)
    push_cast at h
    exact h
  have hup' := hup
  rw [U_iterate_affine_real] at hup'
  have hlow' := hlow
  rw [U_iterate_affine_real] at hlow'
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have h2 : (0 : ℝ) < 2 ^ B' := by positivity
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  -- the main term at step `k` exceeds `x/2`
  set A := 3 ^ k / 2 ^ B' * (M : ℝ) with hAdef
  have hA : x / 2 < A := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- upper bound
    have : 3 ^ (k + 1) / 2 ^ wsum (vword M) (k + 1) * (M : ℝ) ≤ x := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    linarith
  · -- first lower bound
    rw [div_le_iff₀ (by positivity)]
    rw [hAdef, div_mul_eq_mul_div, lt_div_iff₀ h2] at hA
    rw [pow_succ]
    nlinarith
  · -- second lower bound: `2^b ≤ 3 U^k(M) + 1 ≤ 8 A`
    have hstep : (U^[k + 1] M : ℚ) = (3 * (U^[k] M : ℚ) + 1) / 2 ^ b := by
      rw [Function.iterate_succ_apply', U_cast]; rfl
    have hge1 : (1 : ℝ) ≤ (U^[k + 1] M : ℝ) := by
      have := (odd_U_iterate hM (k + 1)).pos
      exact_mod_cast this
    have hstepR : (U^[k + 1] M : ℝ) = (3 * (U^[k] M : ℝ) + 1) / 2 ^ b := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hstep
      push_cast at this
      exact this
    have hUk : (U^[k] M : ℝ) = A + ((offset (vword M) k : ℚ) : ℝ) := by
      rw [U_iterate_affine_real]
    have hx0 : 0 < x := by have : (0 : ℝ) < (3 / 2) ^ k := by positivity
                           linarith
    have hUk1 : (1 : ℝ) ≤ (U^[k] M : ℝ) := by
      have := (odd_U_iterate hM k).pos
      exact_mod_cast this
    have hb8 : (2 : ℝ) ^ b ≤ 8 * A := by
      rw [hstepR, le_div_iff₀ h2b] at hge1
      linarith
    rw [div_le_iff₀ (by positivity), hw, pow_add, pow_succ]
    rw [hAdef, show (8 : ℝ) * (3 ^ k / 2 ^ B' * M) = 8 * 3 ^ k * M / 2 ^ B' by ring,
      le_div_iff₀ h2] at hb8
    nlinarith

/-- The total of the first `k+1` letters of `M`, when they form the word `w`. -/
lemma wsum_of_word {M k S : ℕ} {w : Fin (k + 1) → ℕ} (hw : w ∈ words (k + 1) S)
    (hMw : (fun i : Fin (k + 1) => vword M i) = w) : wsum (vword M) (k + 1) = S := by
  rw [mem_words] at hw
  rw [← hw.1, wsum, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => congrFun hMw i

lemma last_of_word {M k : ℕ} {w : Fin (k + 1) → ℕ}
    (hMw : (fun i : Fin (k + 1) => vword M i) = w) : vword M k = w (Fin.last k) := by
  have := congrFun hMw (Fin.last k)
  simpa using this

/-- **Spacing in a fiber.** Two odd numbers with the same first `k+1` letters `w` (total `S`) and
the same residue mod `3^r` differ by a multiple of `Q = 2^{S+1} 3^r`. -/
lemma fiber_spaced {M M' k S r : ℕ} {w : Fin (k + 1) → ℕ} (hw : w ∈ words (k + 1) S)
    (hM : Odd M) (hM' : Odd M') (hMw : (fun i : Fin (k + 1) => vword M i) = w)
    (hMw' : (fun i : Fin (k + 1) => vword M' i) = w)
    (hz : (M : ZMod (3 ^ r)) = M') (hlt : M' < M) :
    M' + 2 ^ (S + 1) * 3 ^ r ≤ M := by
  obtain ⟨c0, hc⟩ := prefix_iff_modEq (vword_pos hM) (k + 1)
  rw [wsum_of_word hw hMw] at hc
  have h1 : M ≡ c0 [MOD 2 ^ (S + 1)] := (hc M).mp ⟨hM, fun i _ => rfl⟩
  have h1' : M' ≡ c0 [MOD 2 ^ (S + 1)] := (hc M').mp ⟨hM', fun i hi => by
    have := congrFun (hMw'.trans hMw.symm) ⟨i, hi⟩
    simpa using this⟩
  have h2 : M' ≡ M [MOD 3 ^ r] := ((ZMod.natCast_eq_natCast_iff _ _ _).mp hz).symm
  have hcop : Nat.Coprime (2 ^ (S + 1)) (3 ^ r) := Nat.Coprime.pow _ _ (by norm_num)
  have hmod : M' ≡ M [MOD 2 ^ (S + 1) * 3 ^ r] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1'.trans h1.symm, h2⟩
  have hdvd := (Nat.modEq_iff_dvd' hlt.le).mp hmod
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **The bound on one fiber.** For a finite set `F` of odd `M` crossing below `x` at step `k+1`
with first letters `w` (total `S`, last letter `b`) and a fixed residue mod `3^r`,
`3^r ∑_F 1/M ≤ min(3^r/K₀ₐ, 3^r/K₀_b) + b 2^{-S}/2`, where
`K₀ₐ = (3/2)(2^S/2^b) x/3^{k+1}` and `K₀_b = (3/8) 2^S/3^{k+1}`. -/
theorem fiber_bound {x : ℝ} {k S r : ℕ} (hx : 2 * (3 / 2 : ℝ) ^ k ≤ x) {w : Fin (k + 1) → ℕ}
    (hw : w ∈ words (k + 1) S) (z : ZMod (3 ^ r)) (F : Finset ℕ)
    (hF : ∀ M ∈ F, Odd M ∧ (U^[k + 1] M : ℝ) ≤ x ∧ x < (U^[k] M : ℝ) ∧
      (fun i : Fin (k + 1) => vword M i) = w ∧ (M : ZMod (3 ^ r)) = z) :
    (3 : ℝ) ^ r * ∑ M ∈ F, (1 : ℝ) / M ≤
      min ((3 : ℝ) ^ r / (3 / 2 * (2 ^ S / 2 ^ w (Fin.last k)) * x / 3 ^ (k + 1)))
        ((3 : ℝ) ^ r / ((3 / 8 : ℝ) * 2 ^ S / 3 ^ (k + 1))) +
      w (Fin.last k) * (1 / 2 : ℝ) ^ S / 2 := by
  set b := w (Fin.last k)
  have hx0 : 0 < x := by have : (0 : ℝ) < (3 / 2) ^ k := by positivity
                         linarith
  set K0a : ℝ := 3 / 2 * (2 ^ S / 2 ^ b) * x / 3 ^ (k + 1) with hK0a
  set K0b : ℝ := (3 / 8 : ℝ) * 2 ^ S / 3 ^ (k + 1) with hK0b
  set K1 : ℝ := 2 ^ S * x / 3 ^ (k + 1) with hK1
  have hKa : 0 < K0a := by positivity
  have hKb : 0 < K0b := by positivity
  have hmin0 : 0 ≤ min ((3 : ℝ) ^ r / K0a) ((3 : ℝ) ^ r / K0b) := le_min (by positivity) (by positivity)
  rcases F.eq_empty_or_nonempty with rfl | ⟨M0, hM0⟩
  · simp only [sum_empty, mul_zero]; positivity
  -- bounds for each member
  have hmem : ∀ M ∈ F, max K0a K0b ≤ M ∧ (M : ℝ) ≤ K1 := by
    intro M hM
    obtain ⟨hMo, hup, hlow, hMw, -⟩ := hF M hM
    obtain ⟨h1, h2, h3⟩ := Mbounds hMo hx hup hlow
    have hS := wsum_of_word hw hMw
    have hb := last_of_word hMw
    have hw' : wsum (vword M) (k + 1) = wsum (vword M) k + vword M k := Finset.sum_range_succ _ _
    have hpow : (2 : ℝ) ^ wsum (vword M) k = 2 ^ S / 2 ^ b := by
      have hb' : vword M k = b := hb
      rw [eq_div_iff (by positivity), ← pow_add, ← hS, hw', hb']
    rw [hS] at h1 h3
    rw [hpow] at h2
    exact ⟨max_le h2 h3, h1⟩
  have hK0 : 0 < max K0a K0b := lt_max_of_lt_left hKa
  have hKK : max K0a K0b ≤ K1 := ((hmem M0 hM0).1).trans (hmem M0 hM0).2
  have hQ : (0 : ℝ) < 2 ^ (S + 1) * 3 ^ r := by positivity
  have hsum := sum_inv_spaced_le hQ hK0 hKK F hmem (fun M hM M' hM' hlt => by
    obtain ⟨hMo, -, -, hMw, hMz⟩ := hF M hM
    obtain ⟨hMo', -, -, hMw', hMz'⟩ := hF M' hM'
    have := fiber_spaced hw hMo hMo' hMw hMw' (hMz.trans hMz'.symm) hlt
    exact_mod_cast this)
  -- `log(K₁/K₀) ≤ b`
  have hlog : Real.log (K1 / max K0a K0b) ≤ b := by
    have hratio : K1 / K0a = 2 / 3 * 2 ^ b := by
      rw [hK1, hK0a]; field_simp
    have hle : K1 / max K0a K0b ≤ 2 ^ b := by
      calc K1 / max K0a K0b ≤ K1 / K0a :=
            div_le_div_of_nonneg_left (by positivity) hKa (le_max_left _ _)
        _ = 2 / 3 * 2 ^ b := hratio
        _ ≤ 2 ^ b := by have : (0 : ℝ) < 2 ^ b := by positivity
                        linarith
    have hpos : 0 < K1 / max K0a K0b := by positivity
    calc Real.log (K1 / max K0a K0b) ≤ Real.log (2 ^ b) := Real.log_le_log hpos hle
      _ = b * Real.log 2 := by rw [Real.log_pow]
      _ ≤ b * 1 := by
          gcongr
          have := Real.log_two_lt_d9; linarith
      _ = b := mul_one _
  have h3r : (0 : ℝ) < 3 ^ r := by positivity
  calc (3 : ℝ) ^ r * ∑ M ∈ F, (1 : ℝ) / M
      ≤ 3 ^ r * (1 / max K0a K0b + Real.log (K1 / max K0a K0b) / (2 ^ (S + 1) * 3 ^ r)) :=
        mul_le_mul_of_nonneg_left hsum h3r.le
    _ = 3 ^ r / max K0a K0b + Real.log (K1 / max K0a K0b) * (1 / 2) ^ S / 2 := by
        rw [one_div_pow, pow_succ]; field_simp
    _ ≤ min ((3 : ℝ) ^ r / K0a) ((3 : ℝ) ^ r / K0b) + b * (1 / 2 : ℝ) ^ S / 2 := by
        gcongr
        exact le_min (div_le_div_of_nonneg_left h3r.le hKa (le_max_left _ _))
          (div_le_div_of_nonneg_left h3r.le hKb (le_max_right _ _))

/-- **The case split of the paper** (`2^B ≤ x^{1/2}` or not), with `q = x^{1/4}`:
`min(3^r/K₀ₐ, 3^r/K₀_b) ≤ 3^{r+k+1} ((2/3) x^{-1/2} 2^{-S} + (8/3) x^{-1/4} 2^{-S/2})`. -/
lemma min_term_le {x q : ℝ} {k S r b : ℕ} (hbS : b ≤ S) (hx0 : 0 < x) (hq0 : 0 < q)
    (hq : q ^ 2 = √x) :
    min ((3 : ℝ) ^ r / (3 / 2 * (2 ^ S / 2 ^ b) * x / 3 ^ (k + 1)))
        ((3 : ℝ) ^ r / ((3 / 8 : ℝ) * 2 ^ S / 3 ^ (k + 1))) ≤
      3 ^ (r + k + 1) * (2 / 3 / √x * (1 / 2) ^ S + 8 / 3 / q * (1 / √2) ^ S) := by
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hss : √x * √x = x := Real.mul_self_sqrt hx0.le
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have h3 : (0 : ℝ) < 3 ^ (r + k + 1) := by positivity
  have e1 : (3 : ℝ) ^ r / (3 / 2 * (2 ^ S / 2 ^ b) * x / 3 ^ (k + 1)) =
      3 ^ (r + k + 1) * (2 / 3 * 2 ^ b / (2 ^ S * x)) := by
    rw [show (3 : ℝ) ^ (r + k + 1) = 3 ^ r * 3 ^ (k + 1) by ring]; field_simp
  have e2 : (3 : ℝ) ^ r / ((3 / 8 : ℝ) * 2 ^ S / 3 ^ (k + 1)) =
      3 ^ (r + k + 1) * (8 / 3 / 2 ^ S) := by
    rw [show (3 : ℝ) ^ (r + k + 1) = 3 ^ r * 3 ^ (k + 1) by ring]; field_simp
  have hA0 : 0 ≤ 2 / 3 / √x * (1 / 2 : ℝ) ^ S := by positivity
  have hB0 : 0 ≤ 8 / 3 / q * (1 / √2 : ℝ) ^ S := by positivity
  rcases le_or_gt ((2 : ℝ) ^ S) √x with h | h
  · refine (min_le_left _ _).trans ?_
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ h3.le
    have hbx : (2 : ℝ) ^ b ≤ √x := (pow_le_pow_right₀ (by norm_num) hbS).trans h
    have : 2 / 3 * 2 ^ b / (2 ^ S * x) ≤ 2 / 3 / √x * (1 / 2 : ℝ) ^ S := by
      rw [one_div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2 ^ b * √x ≤ x := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 h2S.le]
    linarith
  · refine (min_le_right _ _).trans ?_
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ h3.le
    set t : ℝ := √2 ^ S with ht
    have ht0 : 0 < t := by positivity
    have ht2 : t ^ 2 = 2 ^ S := by
      rw [ht, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    have hqt : q < t := by
      by_contra hc
      push Not at hc
      have : t ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ ht0.le hc 2
      linarith
    have hinv : (1 / √2 : ℝ) ^ S = 1 / t := by rw [one_div_pow]
    have : 8 / 3 / (2 : ℝ) ^ S ≤ 8 / 3 / q * (1 / √2) ^ S := by
      rw [hinv, ← ht2, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma one_div_sqrt_two_lt : (1 / √2 : ℝ) < 1 := by
  have h1 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_one (by positivity)]; exact h1

lemma sqrt_two_ratio : (1 / √2 : ℝ) / (1 - 1 / √2) = 1 + √2 := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (1 : ℝ) - 1 / √2 ≠ 0 := by have := one_div_sqrt_two_lt; linarith
  rw [div_eq_iff hne]
  field_simp
  nlinarith

/-- **Summation over words** of the per-fiber bound. -/
lemma sum_words_bound (k K : ℕ) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    ∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S,
        (c1 * (1 / 2 : ℝ) ^ S + c2 * (1 / √2) ^ S + w (Fin.last k) * (1 / 2 : ℝ) ^ S / 2) ≤
      c1 + c2 * (1 + √2) ^ (k + 1) + 1 := by
  have hA := sum_words_pow_le (r := 1 / 2) (by norm_num) (by norm_num) K (k + 1)
  have hB := sum_words_pow_le (r := 1 / √2) (by positivity) one_div_sqrt_two_lt K (k + 1)
  have hC := sum_words_last_le k K
  rw [sqrt_two_ratio] at hB
  rw [show (1 / 2 : ℝ) / (1 - 1 / 2) = 1 by norm_num, one_pow] at hA
  have e : ∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S,
        (c1 * (1 / 2 : ℝ) ^ S + c2 * (1 / √2) ^ S + w (Fin.last k) * (1 / 2 : ℝ) ^ S / 2) =
      c1 * (∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S, (1 / 2 : ℝ) ^ S) +
        c2 * (∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S, (1 / √2 : ℝ) ^ S) +
        (∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S, (w (Fin.last k) : ℝ) * (1 / 2) ^ S) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hA hc1
  have h2 := mul_le_mul_of_nonneg_left hB hc2
  linarith

/-- **Proposition 5.5 (harmonic bound).** For large `x` (`Large x`), every `E ⊆ 𝓜_x`, every
depth `r` with `r + m ≤ n₀` and every residue `z mod 3^r`,
`H_r(z) = 3^r ∑_{M ∈ E, M ≡ z (3^r)} 1/M ≤ 5`. -/
theorem harmonic {x : ℝ} (hL : Large x) (E : Finset ℕ) (hE : (↑E : Set ℕ) ⊆ Mset x) {r : ℕ}
    (hr : r + mT x ≤ n0 x) (z : ZMod (3 ^ r)) :
    (3 : ℝ) ^ r * ∑ M ∈ E.filter (fun M : ℕ => (M : ZMod (3 ^ r)) = z), (1 : ℝ) / M ≤ 5 := by
  obtain ⟨k, hk⟩ : ∃ k, mT x = k + 1 := ⟨mT x - 1, by have := hL.m_ge; omega⟩
  have hx0 : 0 < x := by have := hL.x_gt; linarith
  -- numerics: `q = x^{1/4}`, `3^{n₀} (1+√2)^m ≤ q`, `2 (3/2)^k ≤ x`
  set q := √(√x) with hqdef
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hq0 : 0 < q := Real.sqrt_pos.mpr hsx
  have hq2 : q ^ 2 = √x := Real.sq_sqrt hsx.le
  have hq4 : q ^ 4 = x := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hq2, Real.sq_sqrt hx0.le]
  have hxexp : Real.exp (Lx x) = x := Real.exp_log hx0
  have hx16 : 16 ≤ x := by
    have := Real.add_one_le_exp (Lx x); have := hL.L_ge; linarith
  have hq2' : 2 ≤ q := by
    by_contra h; push Not at h
    have : q ^ 4 < 2 ^ 4 := pow_lt_pow_left₀ h hq0.le (by norm_num)
    linarith
  set P : ℝ := 3 ^ n0 x * (1 + √2) ^ (k + 1) with hP
  have hP0 : 0 < P := by positivity
  have hPq : P ≤ q := by
    have hP4 : P ^ 4 ≤ x := by
      have e3 : (3 : ℝ) ^ n0 x = Real.exp (n0 x * bet) := by
        rw [Real.exp_nat_mul, bet, Real.exp_log (by norm_num)]
      have e2 : (1 + √2 : ℝ) ^ (k + 1) = Real.exp ((k + 1 : ℕ) * Real.log (1 + √2)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      have hh := hL.harm
      rw [hk] at hh
      rw [hP, e3, e2, ← Real.exp_add, ← Real.exp_nat_mul]
      calc Real.exp (((4 : ℕ) : ℝ) * (n0 x * bet + ((k + 1 : ℕ) : ℝ) * Real.log (1 + √2)))
          ≤ Real.exp (Lx x) := by
            apply Real.exp_le_exp.mpr
            push_cast at hh ⊢
            linarith
        _ = x := hxexp
    rw [← hq4] at hP4
    exact (pow_le_pow_iff_left₀ hP0.le hq0.le (by norm_num)).mp hP4
  have h1P : (1 : ℝ) ≤ (1 + √2) ^ (k + 1) :=
    one_le_pow₀ (by have := Real.sqrt_nonneg 2; linarith)
  have h3P : (3 : ℝ) ^ n0 x ≤ P := le_mul_of_one_le_right (by positivity) h1P
  have hx32 : 2 * (3 / 2 : ℝ) ^ k ≤ x := by
    have : (3 / 2 : ℝ) ^ k ≤ (1 + √2) ^ (k + 1) := by
      calc (3 / 2 : ℝ) ^ k ≤ (1 + √2) ^ k := by
            gcongr
            have : (1 / 2 : ℝ) ≤ √2 := by
              rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
            linarith
        _ ≤ (1 + √2) ^ (k + 1) := pow_le_pow_right₀ (by
            have := Real.sqrt_nonneg 2; linarith) (by omega)
    have h3 : (1 : ℝ) ≤ 3 ^ n0 x := one_le_pow₀ (by norm_num)
    have : (1 + √2) ^ (k + 1) ≤ q := by
      calc (1 + √2 : ℝ) ^ (k + 1) ≤ P := le_mul_of_one_le_left (by positivity) h3
        _ ≤ q := hPq
    have hq3 : 2 * q ≤ x := by
      have h8 : (2 : ℝ) ^ 3 ≤ q ^ 3 := pow_le_pow_left₀ (by norm_num) hq2' 3
      rw [← hq4, show q ^ 4 = q * q ^ 3 by ring]
      nlinarith [mul_le_mul_of_nonneg_left h8 hq0.le]
    linarith
  have h3r : (3 : ℝ) ^ (r + k + 1) ≤ 3 ^ n0 x := pow_le_pow_right₀ (by norm_num) (by omega)
  -- the fiber decomposition by the word of the next `m` steps
  set E' := E.filter (fun M : ℕ => (M : ZMod (3 ^ r)) = z) with hE'
  set g : ℕ → (Fin (k + 1) → ℕ) := fun M i => vword M i with hg
  set K := E'.sup (fun M => wsum (vword M) (k + 1)) with hK
  have hmemE : ∀ M ∈ E', Odd M ∧ (U^[k + 1] M : ℝ) ≤ x ∧ x < (U^[k] M : ℝ) ∧
      (M : ZMod (3 ^ r)) = z := by
    intro M hM
    rw [hE', Finset.mem_filter] at hM
    obtain ⟨hMo, hcr, hpT, -⟩ := hE hM.1
    rw [hk] at hpT
    refine ⟨hMo, ?_, ?_, hM.2⟩
    · have := passT_spec hcr; rwa [hpT] at this
    · exact lt_of_lt_passT (by omega)
  have hmaps : ∀ M ∈ E', g M ∈ (range (K + 1)).biUnion (fun S => words (k + 1) S) := by
    intro M hM
    rw [Finset.mem_biUnion]
    refine ⟨wsum (vword M) (k + 1), ?_, ?_⟩
    · rw [mem_range, Nat.lt_succ_iff]
      exact Finset.le_sup (f := fun M => wsum (vword M) (k + 1)) hM
    · rw [mem_words]
      refine ⟨?_, fun i => vword_pos (hmemE M hM).1 i⟩
      rw [wsum, ← Fin.sum_univ_eq_sum_range]
  have hdisj : (↑(range (K + 1)) : Set ℕ).PairwiseDisjoint (fun S => words (k + 1) S) := by
    intro S _ S' _ hSS'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [mem_words] at hw hw'
    exact hSS' (hw.1.symm.trans hw'.1)
  have hdec : ∑ M ∈ E', (1 : ℝ) / M = ∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S,
      ∑ M ∈ E' with g M = w, (1 : ℝ) / M := by
    rw [← Finset.sum_biUnion hdisj, Finset.sum_fiberwise_of_maps_to hmaps]
  -- per-fiber bound
  have hfib : ∀ S ∈ range (K + 1), ∀ w ∈ words (k + 1) S,
      (3 : ℝ) ^ r * ∑ M ∈ E' with g M = w, (1 : ℝ) / M ≤
        3 ^ (r + k + 1) * (2 / 3 / √x) * (1 / 2 : ℝ) ^ S +
          3 ^ (r + k + 1) * (8 / 3 / q) * (1 / √2) ^ S +
          w (Fin.last k) * (1 / 2 : ℝ) ^ S / 2 := by
    intro S _ w hw
    have hb : w (Fin.last k) ≤ S := by
      have := (mem_words.mp hw).1
      rw [← this]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
    have h1 := fiber_bound hx32 hw z (E'.filter (fun M => g M = w)) (fun M hM => by
      rw [Finset.mem_filter] at hM
      obtain ⟨a1, a2, a3, a4⟩ := hmemE M hM.1
      exact ⟨a1, a2, a3, hM.2, a4⟩)
    have h2 := min_term_le (k := k) (r := r) hb hx0 hq0 hq2
    calc _ ≤ _ := h1
      _ ≤ _ := by
        rw [add_le_add_iff_right]
        refine h2.trans (le_of_eq ?_)
        ring
  calc (3 : ℝ) ^ r * ∑ M ∈ E', (1 : ℝ) / M
      = ∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S,
          (3 : ℝ) ^ r * ∑ M ∈ E' with g M = w, (1 : ℝ) / M := by
        rw [hdec, Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ ∑ S ∈ range (K + 1), ∑ w ∈ words (k + 1) S,
          (3 ^ (r + k + 1) * (2 / 3 / √x) * (1 / 2 : ℝ) ^ S +
            3 ^ (r + k + 1) * (8 / 3 / q) * (1 / √2) ^ S +
            w (Fin.last k) * (1 / 2 : ℝ) ^ S / 2) :=
        Finset.sum_le_sum fun S hS => Finset.sum_le_sum fun w hw => hfib S hS w hw
    _ ≤ 3 ^ (r + k + 1) * (2 / 3 / √x) + 3 ^ (r + k + 1) * (8 / 3 / q) * (1 + √2) ^ (k + 1) + 1 :=
        sum_words_bound k K (by positivity) (by positivity)
    _ ≤ 2 / 3 + 8 / 3 + 1 := by
        gcongr ?_ + ?_ + 1
        · -- `3^{r+m} ≤ 3^{n₀} ≤ q ≤ √x`
          have hqx : q ≤ √x := by rw [← hq2]; nlinarith
          rw [mul_div_assoc', div_le_iff₀ hsx]
          nlinarith
        · rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hq0]
          have : (3 : ℝ) ^ (r + k + 1) * (1 + √2) ^ (k + 1) ≤ q :=
            (mul_le_mul_of_nonneg_right h3r (by positivity)).trans hPq
          have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 8 / 3)
          linarith
    _ ≤ 5 := by norm_num

end CollatzCLT
