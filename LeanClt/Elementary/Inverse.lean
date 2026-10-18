import LeanClt.Elementary.Affine

/-!
# Lemma 2.1, existence: the inverse source is automatically a positive odd integer

Lemma 2.1 of the paper: for a word `\vec a` of length `r` (letters `≥ 1`) and an odd
`M > 0`, the candidate source `N = 2^S (M - F_r(\vec a)) / 3^r` exists (as an integer)
iff `M ≡ F_r (mod 3^r)` in `ℤ[1/2]`, and then it is automatically a positive odd integer
whose valuation word is `\vec a` and with `U^r(N) = M`.

We take as hypothesis that the right side of (2.2) is an integer `N`. This is the
congruence condition in its most direct form. The proof is the paper's backward recursion
`x_{j-1} = (2^{a_j} x_j - 1)/3`, with integrality of each `x_j` obtained from
`ℤ[1/2] ∩ ℤ[1/3] = ℤ`.
-/

open Function Finset

namespace CollatzCLT

/-- `ℤ[1/2] ∩ ℤ[1/3] = ℤ`, in the form needed: if `2^k q` and `3 q` are integers then so is `q`. -/
lemma rat_int_of_two_pow_three {q : ℚ} {k : ℕ} {A B : ℤ}
    (hA : 2 ^ k * q = A) (hB : 3 * q = B) : ∃ z : ℤ, q = z := by
  have hAB : (3 : ℤ) * A = 2 ^ k * B := by
    have : (3 : ℚ) * A = 2 ^ k * B := by rw [← hA, ← hB]; ring
    exact_mod_cast this
  have hcop : IsCoprime ((2 : ℤ) ^ k) 3 :=
    IsCoprime.pow_left (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have hdvd : (2 : ℤ) ^ k ∣ A := hcop.dvd_of_dvd_mul_left ⟨B, by rw [← hAB]⟩
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, mul_left_cancel₀ (pow_ne_zero k (two_ne_zero : (2 : ℚ) ≠ 0)) ?_⟩
  rw [hA, hz]; push_cast; ring

/-- `2^{S_j} F_j` is an integer. -/
lemma two_pow_mul_offset_int (a : ℕ → ℕ) (j : ℕ) :
    ∃ z : ℤ, (2 : ℚ) ^ wsum a j * offset a j = z := by
  induction j with
  | zero => exact ⟨0, by simp [offset]⟩
  | succ j ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨3 * z + 2 ^ wsum a j, ?_⟩
    simp only [wsum, sum_range_succ, pow_add, offset] at hz ⊢
    push_cast
    rw [← hz]
    field_simp

/-- `v₂(2^a z) = a` for odd `z`. -/
lemma padicValNat_two_pow_mul_odd {a z : ℕ} (hz : Odd z) : padicValNat 2 (2 ^ a * z) = a := by
  have hz0 : z ≠ 0 := by rintro rfl; exact absurd hz (by decide)
  rw [padicValNat.mul (by positivity) hz0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    add_zero]

/-- **Lemma 2.1, existence.** If the inverse formula (2.2) produces an integer `N`, then
`N` is a positive odd integer whose valuation word starts with `a_0, …, a_{r-1}` and
which satisfies `U^r(N) = M`. -/
theorem source_exists {a : ℕ → ℕ} (ha : ∀ i, 1 ≤ a i) {r M : ℕ} (hM : Odd M) {N : ℤ}
    (hN : (N : ℚ) = 2 ^ wsum a r * ((M : ℚ) - offset a r) / 3 ^ r) :
    ∃ n : ℕ, (n : ℤ) = N ∧ Odd n ∧ (∀ i < r, vword n i = a i) ∧ U^[r] n = M := by
  -- the forward affine orbit of the candidate source
  set x : ℕ → ℚ := fun j => affIter a j (N : ℚ) with hx
  have hstep : ∀ j, x (j + 1) = (3 * x j + 1) / 2 ^ a j := fun j => rfl
  have hxr : x r = M := by
    simp only [hx, affIter_eq, hN]
    field_simp
    ring
  -- dyadic integrality: `2^{S_j} x_j ∈ ℤ`
  have hD : ∀ j, ∃ A : ℤ, 2 ^ wsum a j * x j = A := by
    intro j
    obtain ⟨z, hz⟩ := two_pow_mul_offset_int a j
    refine ⟨3 ^ j * N + z, ?_⟩
    simp only [hx, affIter_eq, mul_add, hz]
    push_cast
    field_simp
  -- backward recursion: every `x_j` (`j ≤ r`) is an odd natural number
  have hBack : ∀ k ≤ r, ∃ z : ℕ, Odd z ∧ x (r - k) = z := by
    intro k
    induction k with
    | zero => intro _; exact ⟨M, hM, by simpa using hxr⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, hxz⟩ := ih (by omega)
      have hj1 : r - k = (r - (k + 1)) + 1 := by omega
      rw [hj1, hstep] at hxz
      set j := r - (k + 1)
      have h3 : 3 * x j = 2 ^ a j * z - 1 := by
        field_simp at hxz; linarith
      obtain ⟨A, hA⟩ := hD j
      obtain ⟨w, hw⟩ := rat_int_of_two_pow_three hA (B := 2 ^ a j * z - 1) (by rw [h3]; push_cast; ring)
      -- `3w = 2^{a_j} z - 1` with `z` odd, `a_j ≥ 1`: so `w` is positive and odd
      have hwz : 3 * w = 2 ^ a j * (z : ℤ) - 1 := by
        have : (3 : ℚ) * w = 2 ^ a j * z - 1 := by rw [← hw, h3]
        exact_mod_cast this
      have hz1 : 1 ≤ (z : ℤ) := by exact_mod_cast hz.pos
      have ha2 : (2 : ℤ) ≤ 2 ^ a j := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a j := pow_le_pow_right₀ (by norm_num) (ha j)
      have hwpos : 0 < w := by nlinarith
      have hwodd : Odd w := by
        have heven : Even ((2 : ℤ) ^ a j * z) := by
          obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (ha j)
          rw [hb, pow_add]; exact (even_two.pow_of_ne_zero one_ne_zero).mul_right _ |>.mul_right _
        have h3w : Odd (3 * w) := by rw [hwz]; exact heven.sub_odd odd_one
        exact (Int.odd_mul.mp h3w).2
      refine ⟨w.toNat, ?_, ?_⟩
      · have := hwodd; rwa [← Int.toNat_of_nonneg hwpos.le, Int.odd_coe_nat] at this
      · rw [hw]; exact_mod_cast (Int.toNat_of_nonneg hwpos.le).symm
  have hBack' : ∀ j ≤ r, ∃ z : ℕ, Odd z ∧ x j = z := by
    intro j hj
    have := hBack (r - j) (by omega)
    rwa [Nat.sub_sub_self hj] at this
  -- the source itself
  obtain ⟨n, hn, hxn⟩ := hBack' 0 (Nat.zero_le _)
  have hNn : (N : ℚ) = n := hxn
  refine ⟨n, by exact_mod_cast hNn.symm, hn, ?_⟩
  -- forward induction: the orbit of `n` follows `x`, with the prescribed letters
  have hfwd : ∀ j ≤ r, (U^[j] n : ℚ) = x j ∧ ∀ i < j, vword n i = a i := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp [hx, affIter, hNn], fun i hi => absurd hi (by omega)⟩
    | succ j ih =>
      intro hj
      obtain ⟨hUj, hw⟩ := ih (by omega)
      obtain ⟨zj, -, hzj⟩ := hBack' j (by omega)
      obtain ⟨zj1, hzj1, hzj1'⟩ := hBack' (j + 1) hj
      have hUnat : U^[j] n = zj := by exact_mod_cast hUj.trans hzj
      have hrel : 3 * zj + 1 = 2 ^ a j * zj1 := by
        have h := hstep j
        rw [hzj, hzj1'] at h
        have : (3 * zj + 1 : ℚ) = 2 ^ a j * zj1 := by
          rw [h]; field_simp
        exact_mod_cast this
      have hval : vword n j = a j := by
        simp only [vword, hUnat, hrel, padicValNat_two_pow_mul_odd hzj1]
      refine ⟨?_, ?_⟩
      · rw [iterate_succ_apply', U_cast, hUj]
        simp only [vword] at hval
        rw [hUnat] at hval ⊢
        rw [hval, hstep, hzj]
        rfl
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hw i hi
        · exact hval
  obtain ⟨hUr, hwr⟩ := hfwd r le_rfl
  refine ⟨hwr, ?_⟩
  exact_mod_cast hUr.trans hxr

end CollatzCLT
