import LeanClt.Renewal.Defs

/-!
# Lemma 2.2(ii): the negative-binomial law of `S_t`

From the convolution definition we derive the two-term recursion
`P(S_{t+1} = A+1) = ½ (P(S_t = A) + P(S_{t+1} = A))`
(memorylessness: the last letter is `1`, or it is `≥ 2` and then is one more than a fresh
letter), and from it, with Pascal's rule, the closed form
`P(S_{t+1} = A+1) = C(A, t) 2^{-(A+1)}`, valid for all `t, A ≥ 0` (both sides vanish for
`A < t`).
-/

open Finset

namespace CollatzCLT

@[simp] lemma lawS_zero_zero : lawS 0 0 = 1 := by simp [lawS]

@[simp] lemma lawS_zero_succ (A : ℕ) : lawS 0 (A + 1) = 0 := by simp [lawS]

@[simp] lemma lawS_succ_zero (t : ℕ) : lawS (t + 1) 0 = 0 := by simp [lawS]

/-- **Memorylessness recursion.** `P(S_{t+1} = A+1) = ½ (P(S_t = A) + P(S_{t+1} = A))`. -/
lemma lawS_succ_succ (t A : ℕ) :
    lawS (t + 1) (A + 1) = (1 / 2) * (lawS t A + lawS (t + 1) A) := by
  rw [lawS, sum_range_succ', lawS, mul_add, mul_sum, add_comm]
  congr 1
  · simp
  · apply sum_congr rfl
    intro k _
    have : A + 1 - 1 - (k + 1) = A - 1 - k := by omega
    rw [this, pow_succ]
    ring

/-- **Closed form.** `P(S_{t+1} = A+1) = C(A, t) · 2^{-(A+1)}` for all `t, A`. -/
theorem lawS_succ_succ_eq (A : ℕ) : ∀ t : ℕ,
    lawS (t + 1) (A + 1) = (A.choose t : ℝ) * (1 / 2 : ℝ) ^ (A + 1) := by
  induction A with
  | zero =>
    intro t
    rw [lawS_succ_succ, lawS_succ_zero]
    cases t with
    | zero => simp
    | succ t => simp
  | succ A ih =>
    intro t
    rw [lawS_succ_succ]
    cases t with
    | zero =>
      rw [lawS_zero_succ, ih 0]
      simp; ring
    | succ t =>
      rw [ih t, ih (t + 1), Nat.choose_succ_succ]
      push_cast
      ring

/-- **Lemma 2.2(ii).** `P(S_t = A) = C(A-1, t-1) 2^{-A}` for `1 ≤ t ≤ A`. -/
theorem lawS_eq_choose {t A : ℕ} (ht : 1 ≤ t) (htA : t ≤ A) :
    lawS t A = ((A - 1).choose (t - 1) : ℝ) * (1 / 2 : ℝ) ^ A := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' ht
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le' (le_trans ht htA)
  simpa using lawS_succ_succ_eq A t

/-- `P(S_t = A) = 0` for `A < t`. -/
theorem lawS_eq_zero_of_lt {t A : ℕ} (h : A < t) : lawS t A = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_le_of_lt (Nat.zero_le A) h)
  rcases A with _ | A
  · simp
  · rw [zero_add, lawS_succ_succ_eq, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma lawS_nonneg (t A : ℕ) : 0 ≤ lawS t A := by
  rcases t with _ | t
  · unfold lawS; split_ifs <;> norm_num
  rcases A with _ | A
  · simp
  · rw [lawS_succ_succ_eq]; positivity

end CollatzCLT
