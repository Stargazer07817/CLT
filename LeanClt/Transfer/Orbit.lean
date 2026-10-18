import LeanClt.Transfer.Lemma51

/-!
# Lemma 5.2 (orbit approximation): the exact logarithmic form

`orbit_log`: for odd `N`, `log U^j(N) = log N - cj - ℓ(S_j - 2j) + D_j` with
`0 ≤ D_j ≤ 2^{S_j}/(2^j N)` (from the affine identity (2.1) and `0 ≤ F_j ≤ (3/2)^j`).
-/

open Real Finset

namespace CollatzCLT

/-- **The logarithmic orbit identity (5.6, `eq:logorbit`)**, with an explicit error. -/
theorem orbit_log {N : ℕ} (hN : Odd N) (j : ℕ) :
    0 ≤ Real.log (U^[j] N) - (Real.log N - c * j - ell * ((Swd N j : ℝ) - 2 * j)) ∧
      Real.log (U^[j] N) - (Real.log N - c * j - ell * ((Swd N j : ℝ) - 2 * j)) ≤
        2 ^ Swd N j / (2 ^ j * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.pos
  set S := Swd N j with hS
  have haff := U_iterate_affine N j
  have hF0 := offset_nonneg (vword N) j
  have hF1 := offset_le (vword N) (fun i => vword_pos hN i) j
  set F : ℝ := ((offset (vword N) j : ℚ) : ℝ) with hFdef
  have hFr0 : 0 ≤ F := by rw [hFdef]; exact_mod_cast hF0
  have hFr1 : F ≤ (3 / 2 : ℝ) ^ j := by
    rw [hFdef]
    have : ((offset (vword N) j : ℚ) : ℝ) ≤ (((3 / 2 : ℚ) ^ j - 1 : ℚ) : ℝ) := by exact_mod_cast hF1
    push_cast at this; linarith
  set P : ℝ := 3 ^ j / 2 ^ S * N with hP
  have hPpos : 0 < P := by positivity
  have hU : (U^[j] N : ℝ) = P + F := by
    have := congrArg (fun q : ℚ => (q : ℝ)) haff
    simp only [Rat.cast_natCast] at this
    rw [this]; push_cast; rfl
  have hlogP : Real.log P = Real.log N - c * j - ell * ((S : ℝ) - 2 * j) := by
    rw [hP, Real.log_mul (by positivity) hN0.ne', Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, c_eq]
    unfold ell bet
    ring
  have hlogU : Real.log (U^[j] N) = Real.log P + Real.log (1 + F / P) := by
    rw [hU, ← Real.log_mul hPpos.ne' (by positivity)]
    congr 1; field_simp
  rw [hlogU, hlogP]
  have hq0 : 0 ≤ F / P := div_nonneg hFr0 hPpos.le
  refine ⟨by simp only [add_sub_cancel_left]; exact Real.log_nonneg (by linarith), ?_⟩
  simp only [add_sub_cancel_left]
  calc Real.log (1 + F / P) ≤ F / P := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + F / P); linarith
    _ ≤ (3 / 2 : ℝ) ^ j / P := by gcongr
    _ = 2 ^ S / (2 ^ j * N) := by
        rw [hP, div_pow]; field_simp

end CollatzCLT
