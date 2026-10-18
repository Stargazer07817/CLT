import LeanClt.Positivity.Transfer

/-!
# §8.2: the block parameters and their numerical facts

The parameters of §8.2, (8.4, `eq:blockparams`), for a scale `b`:

* `Bc t = B(t)`, defined as the least `B` with `3^t ≤ 2^B` (`Nat.clog 2 (3^t)`); it equals the
  paper's `⌈θ t⌉` (`Bc_eq_ceil`), so `3^t ≤ 2^{B(t)} ≤ 2·3^t` (`three_pow_le_two_pow_Bc`,
  `two_pow_Bc_le`);
* `wB b = ⌊3b/5⌋`, `lB b = b - w_b`, `hB b = b + w_b`, `eB b = ⌊b/100⌋`,
  `rB b = 2 w_b - B(w_b) - 2 e_b`, `mB b = ⌈b^{3/5}⌉`;
* `barrier b s = H_b(s) = 2b + B((s-b)_+) - B((b-s)_+)`, with `(·)_+` the truncated subtraction
  of `ℕ`.

The paper takes "b large" without stating thresholds. The facts used later carry explicit ones:
`5 B(t) ≤ 8t + 4` (`five_mul_Bc_le`, from `3^5 ≤ 2^8`), `b^3 ≤ ⌈b^{3/5}⌉^5`
(`pow_three_le_mB_pow_five`), `⌈b^{3/5}⌉ ≤ w_b` for `b ≥ 32` (`mB_le_wB`) and `⌈b^{3/5}⌉ ≥ 12` for
`b ≥ 63` (`twelve_le_mB`). Lemma 8.4 [`lem:C1`], (8.6) and Proposition 8.5 state their
thresholds existentially (`∃ b₁, ∀ b ≥ b₁`); (8.5) carries the explicit hypothesis `b ≥ 32`.
-/

open Finset Real

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Definitions, (8.4, `eq:blockparams`) -/

/-- `B(t)`: the least `B` with `3^t ≤ 2^B`. It is the paper's `⌈θ t⌉` (`Bc_eq_ceil`). -/
def Bc (t : ℕ) : ℕ := Nat.clog 2 (3 ^ t)

/-- `w_b = ⌊3b/5⌋`. -/
def wB (b : ℕ) : ℕ := 3 * b / 5

/-- `ℓ_b = b - w_b`. -/
def lB (b : ℕ) : ℕ := b - wB b

/-- `h_b = b + w_b`. -/
def hB (b : ℕ) : ℕ := b + wB b

/-- `e_b = ⌊b/100⌋`. -/
def eB (b : ℕ) : ℕ := b / 100

/-- `r_b = 2 w_b - B(w_b) - 2 e_b` (truncated subtraction). -/
def rB (b : ℕ) : ℕ := 2 * wB b - Bc (wB b) - 2 * eB b

/-- `⌈b^{3/5}⌉`, the half-width of the central window. -/
def mB (b : ℕ) : ℕ := ⌈(b : ℝ) ^ (3 / 5 : ℝ)⌉₊

/-- The barrier `H_b(s) = 2b + B((s-b)_+) - B((b-s)_+)`. -/
def barrier (b s : ℕ) : ℤ := 2 * b + Bc (s - b) - Bc (b - s)

/-! ## `B(t)` -/

lemma three_pow_le_two_pow_Bc (t : ℕ) : 3 ^ t ≤ 2 ^ Bc t := Nat.le_pow_clog (by norm_num) _

lemma Bc_le_of_le {t B : ℕ} (h : 3 ^ t ≤ 2 ^ B) : Bc t ≤ B := Nat.clog_le_of_le_pow h

@[simp] lemma Bc_zero : Bc 0 = 0 := by simp [Bc]

lemma Bc_mono {t t' : ℕ} (h : t ≤ t') : Bc t ≤ Bc t' :=
  Nat.clog_mono_right 2 (Nat.pow_le_pow_right (by norm_num) h)

lemma one_le_Bc {t : ℕ} (ht : 1 ≤ t) : 1 ≤ Bc t := by
  by_contra h
  have h0 : Bc t = 0 := by omega
  have h1 := three_pow_le_two_pow_Bc t
  rw [h0, pow_zero] at h1
  have : 1 < 3 ^ t := Nat.one_lt_pow (by omega) (by norm_num)
  omega

lemma two_pow_Bc_sub_one_lt {t : ℕ} (ht : 1 ≤ t) : 2 ^ (Bc t - 1) < 3 ^ t := by
  have h1 : 1 < 3 ^ t := Nat.one_lt_pow (by omega) (by norm_num)
  have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  simpa [Bc, Nat.pred_eq_sub_one] using this

/-- `2^{B(t)} ≤ 2·3^t`. -/
lemma two_pow_Bc_le (t : ℕ) : 2 ^ Bc t ≤ 2 * 3 ^ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have hlt := two_pow_Bc_sub_one_lt ht
    have hB := one_le_Bc ht
    calc 2 ^ Bc t = 2 * 2 ^ (Bc t - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * 3 ^ t := by omega

lemma Bc_le_two_mul (t : ℕ) : Bc t ≤ 2 * t := by
  apply Bc_le_of_le
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) t

/-- `5 B(t) ≤ 8t + 4`, from `3^5 ≤ 2^8`. -/
lemma five_mul_Bc_le (t : ℕ) : 5 * Bc t ≤ 8 * t + 4 := by
  set c := (8 * t + 4) / 5 with hc
  have hc' : 8 * t ≤ 5 * c := by omega
  have h : 3 ^ t ≤ 2 ^ c := by
    have h5 : (3 ^ t) ^ 5 ≤ (2 ^ c) ^ 5 := by
      calc (3 ^ t) ^ 5 = 243 ^ t := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 256 ^ t := Nat.pow_le_pow_left (by norm_num) t
        _ = 2 ^ (8 * t) := by rw [pow_mul]; norm_num
        _ ≤ 2 ^ (5 * c) := Nat.pow_le_pow_right (by norm_num) hc'
        _ = (2 ^ c) ^ 5 := by rw [← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
  have := Bc_le_of_le h
  omega

/-- `B(s + t) ≤ B(s) + B(t)`. -/
lemma Bc_add_le (s t : ℕ) : Bc (s + t) ≤ Bc s + Bc t := by
  apply Bc_le_of_le
  rw [pow_add, pow_add]
  exact Nat.mul_le_mul (three_pow_le_two_pow_Bc s) (three_pow_le_two_pow_Bc t)

lemma theta_mul_le_Bc (t : ℕ) : θ * t ≤ Bc t := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((3 : ℝ) ^ t) ≤ (2 : ℝ) ^ Bc t := by exact_mod_cast three_pow_le_two_pow_Bc t
  have hl := Real.log_le_log (by positivity) hc
  rw [Real.log_pow, Real.log_pow] at hl
  unfold θ
  rw [div_mul_eq_mul_div, div_le_iff₀ h2]
  linarith

lemma Bc_sub_one_lt {t : ℕ} (ht : 1 ≤ t) : (Bc t : ℝ) - 1 < θ * t := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ((2 : ℝ) ^ (Bc t - 1)) < (3 : ℝ) ^ t := by exact_mod_cast two_pow_Bc_sub_one_lt ht
  have hl := Real.log_lt_log (by positivity) hc
  rw [Real.log_pow, Real.log_pow, Nat.cast_sub (one_le_Bc ht), Nat.cast_one] at hl
  unfold θ
  rw [div_mul_eq_mul_div, lt_div_iff₀ h2]
  linarith

/-- **`B(t) = ⌈θ t⌉`**, the paper's definition (§8.2). -/
theorem Bc_eq_ceil (t : ℕ) : Bc t = ⌈θ * t⌉₊ := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have hB : Bc t ≠ 0 := by have := one_le_Bc ht; omega
    symm
    rw [Nat.ceil_eq_iff hB]
    refine ⟨?_, theta_mul_le_Bc t⟩
    rw [Nat.cast_sub (one_le_Bc ht), Nat.cast_one]
    exact Bc_sub_one_lt ht

lemma Bc_lt_theta_mul_add_one (t : ℕ) : (Bc t : ℝ) < θ * t + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · linarith [Bc_sub_one_lt ht]

/-! ## The barrier -/

lemma barrier_of_le {b s : ℕ} (h : s ≤ b) : barrier b s = 2 * b - Bc (b - s) := by
  simp [barrier, Nat.sub_eq_zero_of_le h]

lemma barrier_of_ge {b s : ℕ} (h : b ≤ s) : barrier b s = 2 * b + Bc (s - b) := by
  simp [barrier, Nat.sub_eq_zero_of_le h]

/-- The barrier is nondecreasing in the depth. -/
lemma barrier_mono (b : ℕ) {j s : ℕ} (h : j ≤ s) : barrier b j ≤ barrier b s := by
  unfold barrier
  have h1 := Bc_mono (show j - b ≤ s - b by omega)
  have h2 := Bc_mono (show b - s ≤ b - j by omega)
  omega

/-- `H_b(s) ≤ 2b + 2(s - b)_+`. -/
lemma barrier_le (b s : ℕ) : barrier b s ≤ 2 * b + 2 * (s - b : ℕ) := by
  unfold barrier
  have := Bc_le_two_mul (s - b)
  omega

/-- `H_b(s) ≥ 2s` before the scale. -/
lemma two_mul_le_barrier {b s : ℕ} (h : s ≤ b) : 2 * (s : ℤ) ≤ barrier b s := by
  rw [barrier_of_le h]
  have := Bc_le_two_mul (b - s)
  omega

/-! ## The window `⌈b^{3/5}⌉` -/

lemma rpow_three_fifths_pow_five (b : ℕ) : ((b : ℝ) ^ (3 / 5 : ℝ)) ^ 5 = (b : ℝ) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b)]; norm_num

/-- `b^3 ≤ ⌈b^{3/5}⌉^5`. -/
lemma pow_three_le_mB_pow_five (b : ℕ) : b ^ 3 ≤ mB b ^ 5 := by
  have hx : (b : ℝ) ^ (3 / 5 : ℝ) ≤ mB b := Nat.le_ceil _
  have h0 : 0 ≤ (b : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have := pow_le_pow_left₀ h0 hx 5
  rw [rpow_three_fifths_pow_five] at this
  exact_mod_cast this

/-- `⌈b^{3/5}⌉ ≤ w_b` for `b ≥ 32`. -/
lemma mB_le_wB {b : ℕ} (hb : 32 ≤ b) : mB b ≤ wB b := by
  unfold mB wB
  apply Nat.ceil_le.mpr
  have hb' : (32 : ℝ) ≤ b := by exact_mod_cast hb
  have h0 : 0 ≤ (b : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have hx : (b : ℝ) ^ (3 / 5 : ℝ) ≤ b / 4 := by
    have h5 : ((b : ℝ) ^ (3 / 5 : ℝ)) ^ 5 ≤ ((b : ℝ) / 4) ^ 5 := by
      rw [rpow_three_fifths_pow_five, div_pow]
      rw [le_div_iff₀ (by norm_num)]
      have hb2 : (1024 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
      have hb3 : (0 : ℝ) ≤ (b : ℝ) ^ 3 := by positivity
      calc (b : ℝ) ^ 3 * 4 ^ 5 = (b : ℝ) ^ 3 * 1024 := by norm_num
        _ ≤ (b : ℝ) ^ 3 * (b : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hb2 hb3
        _ = (b : ℝ) ^ 5 := by ring
    exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp h5
  have hq : 3 * b ≤ 5 * (3 * b / 5) + 4 := by omega
  have hq' : (3 : ℝ) * b ≤ 5 * ((3 * b / 5 : ℕ) : ℝ) + 4 := by exact_mod_cast hq
  linarith

/-- `⌈b^{3/5}⌉ ≥ 12` for `b ≥ 63`. -/
lemma twelve_le_mB {b : ℕ} (hb : 63 ≤ b) : 12 ≤ mB b := by
  by_contra h
  have h1 : mB b ^ 5 ≤ 11 ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h2 := pow_three_le_mB_pow_five b
  have h3 : 63 ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hb 3
  norm_num at h1 h3
  omega

lemma wB_lt {b : ℕ} (hb : 1 ≤ b) : wB b < b := by unfold wB; omega

lemma hB_le (b : ℕ) : hB b ≤ 2 * b := by unfold hB wB; omega

lemma mB_le_self {b : ℕ} (hb : 32 ≤ b) : mB b ≤ b :=
  (mB_le_wB hb).trans (wB_lt (by omega)).le

end Positivity
end CollatzCLT
