import LeanClt.Transfer.Typical

/-!
# Residues of words: the source-order residue, reversal and truncation

* `Fres a r = K_r(a) · 2^{-S_r} mod 3^r`, the residue `F_r(a) mod 3^r` of the offset in source
  order (letter `a₀` is the first step out of the source).
* `U_cast_Fres`: `U^r(N) ≡ F_r(a^{(r)}(N)) (mod 3^r)`.
* `Xmod_rev`: reversing a word turns the source-order residue into the target-outward residue of
  §2.2, `F_r(a) ≡ X̃_r(a ∘ rev)`; `sum_words_rev` is the induced identity of word sums
  (reversal preserves the total, hence `2^{-S}`).
* `cast_Xmod_append`: the target-outward residue mod `3^m` only depends on the first `m` letters,
  `X_r ≡ X_m (mod 3^m)`.
-/

open Finset

namespace CollatzCLT

lemma isUnit_two_zmod (n : ℕ) : IsUnit (2 : ZMod (3 ^ n)) := by
  have : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by decide)
  have h := (ZMod.unitOfCoprime 2 this).isUnit
  simpa using h

lemma two_mul_half (n : ℕ) : (2 : ZMod (3 ^ n)) * half n = 1 := by
  unfold half
  exact ZMod.mul_inv_of_unit _ (isUnit_two_zmod n)

lemma two_pow_mul_half_pow (n k : ℕ) : (2 : ZMod (3 ^ n)) ^ k * half n ^ k = 1 := by
  rw [← mul_pow, two_mul_half, one_pow]

lemma wsum_mono (a : ℕ → ℕ) {j r : ℕ} (h : j ≤ r) : wsum a j ≤ wsum a r :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- `K_r(a) = ∑_{j<r} 3^{r-1-j} 2^{S_j}`. -/
lemma Kint_eq_sum (a : ℕ → ℕ) (r : ℕ) :
    Kint a r = ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ wsum a j := by
  induction r with
  | zero => simp [Kint]
  | succ r ih =>
    rw [Kint, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj := mem_range.mp hj
      rw [← mul_assoc, ← pow_succ']
      congr 2; omega
    · simp

/-- The residue `F_r(a) mod 3^r` (source order). -/
noncomputable def Fres (a : ℕ → ℕ) (r : ℕ) : ZMod (3 ^ r) :=
  (Kint a r : ZMod (3 ^ r)) * half r ^ wsum a r

lemma Fres_eq_sum (a : ℕ → ℕ) (r : ℕ) :
    Fres a r = ∑ j ∈ range r, (3 : ZMod (3 ^ r)) ^ (r - 1 - j) * half r ^ (wsum a r - wsum a j) := by
  rw [Fres, Kint_eq_sum]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hle := wsum_mono a (mem_range.mp hj).le
  rw [show half r ^ wsum a r = half r ^ (wsum a r - wsum a j) * half r ^ wsum a j by
    rw [← pow_add]; congr 1; omega]
  calc (3 : ZMod (3 ^ r)) ^ (r - 1 - j) * 2 ^ wsum a j *
        (half r ^ (wsum a r - wsum a j) * half r ^ wsum a j)
      = 3 ^ (r - 1 - j) * half r ^ (wsum a r - wsum a j) *
          (2 ^ wsum a j * half r ^ wsum a j) := by ring
    _ = _ := by rw [two_pow_mul_half_pow, mul_one]

lemma Fres_congr {a b : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, a i = b i) : Fres a r = Fres b r := by
  rw [Fres, Fres, Kint_congr h, wsum_congr h]

lemma three_pow_eq_zero {m j : ℕ} (h : m ≤ j) : (3 : ZMod (3 ^ m)) ^ j = 0 := by
  rw [show j = m + (j - m) by omega, pow_add]
  have : (3 : ZMod (3 ^ m)) ^ m = 0 := by
    have := ZMod.natCast_self (3 ^ m); push_cast at this; exact this
  rw [this, zero_mul]

/-- `2^{S_r} U^r(N) = 3^r N + K_r` in `ℕ`. -/
lemma two_pow_mul_U (N r : ℕ) :
    2 ^ wsum (vword N) r * U^[r] N = 3 ^ r * N + Kint (vword N) r := by
  have hU := U_iterate_affine N r
  have hK := Kint_cast (vword N) r
  have : (2 ^ wsum (vword N) r * U^[r] N : ℚ) = 3 ^ r * N + Kint (vword N) r := by
    rw [hU, hK]; field_simp
  exact_mod_cast this

/-- **`U^r(N) ≡ F_r(a^{(r)}(N)) (mod 3^r)`.** -/
lemma U_cast_Fres (N r : ℕ) : (U^[r] N : ZMod (3 ^ r)) = Fres (vword N) r := by
  have h := congrArg (fun k : ℕ => (k : ZMod (3 ^ r))) (two_pow_mul_U N r)
  push_cast at h
  rw [three_pow_eq_zero le_rfl, zero_mul, zero_add] at h
  rw [Fres, ← h, mul_comm, ← mul_assoc, mul_comm (half r ^ _), two_pow_mul_half_pow, one_mul]

/-- Conversely, a residue condition `M ≡ F_r(a)` makes `2^{S} M - K_r(a)` divisible by `3^r`. -/
lemma dvd_of_cast_Fres {a : ℕ → ℕ} {r M : ℕ} (h : (M : ZMod (3 ^ r)) = Fres a r) :
    ((3 ^ r : ℕ) : ℤ) ∣ 2 ^ wsum a r * (M : ℤ) - Kint a r := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h, Fres, mul_comm (Kint a r : ZMod (3 ^ r)), ← mul_assoc, two_pow_mul_half_pow, one_mul,
    sub_self]

/-! ## Reversal -/

/-- The prefix sums of a `Fin`-word in `ℕ`-indexed form. -/
lemma psum_eq {r : ℕ} (a : Fin r → ℕ) (j : Fin r) : psum a j = wsum (ext a) (j + 1) := by
  unfold psum wsum
  have e : ∀ i : Fin r, (if i ≤ j then a i else 0) =
      (fun k : ℕ => if k ≤ (j : ℕ) then ext a k else 0) i := by
    intro i
    simp only [ext, i.isLt, ↓reduceDIte, Fin.eta, Fin.le_iff_val_le_val]
  rw [Finset.sum_congr rfl (fun i _ => e i), Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ (j : ℕ) then ext a k else 0), ← Finset.sum_filter]
  congr 1
  ext k; simp only [mem_filter, mem_range]; omega

/-- `X_n` as an `ℕ`-indexed sum. -/
lemma Xmod_eq_sum {r : ℕ} (a : Fin r → ℕ) :
    Xmod a = ∑ j ∈ range r, (3 : ZMod (3 ^ r)) ^ j * half r ^ wsum (ext a) (j + 1) := by
  unfold Xmod
  rw [← Fin.sum_univ_eq_sum_range (fun j => (3 : ZMod (3 ^ r)) ^ j * half r ^ wsum (ext a) (j + 1))]
  exact Finset.sum_congr rfl fun j _ => by rw [psum_eq]

lemma ext_rev {r : ℕ} (a : Fin r → ℕ) {i : ℕ} (hi : i < r) :
    ext (a ∘ Fin.rev) i = ext a (r - 1 - i) := by
  simp only [ext, hi, ↓reduceDIte, Function.comp_apply, show r - 1 - i < r by omega]
  congr 1
  ext; simp [Fin.val_rev]; omega

/-- Prefix sums of the reversed word are suffix sums. -/
lemma wsum_ext_rev {r : ℕ} (a : Fin r → ℕ) {j : ℕ} (hj : j < r) :
    wsum (ext (a ∘ Fin.rev)) (j + 1) = wsum (ext a) r - wsum (ext a) (r - 1 - j) := by
  have h1 : wsum (ext (a ∘ Fin.rev)) (j + 1) = ∑ i ∈ range (j + 1), ext a (r - 1 - i) := by
    unfold wsum
    exact Finset.sum_congr rfl fun i hi => ext_rev a (by have := mem_range.mp hi; omega)
  have h2 : ∑ i ∈ range (j + 1), ext a (r - 1 - i) = ∑ i ∈ Ico (r - 1 - j) r, ext a i := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_reflect (ext a) 0 (n := r - 1) (by omega),
      show r - 1 + 1 - (j + 1) = r - 1 - j by omega, show r - 1 + 1 - 0 = r by omega]
  have h3 : wsum (ext a) r = wsum (ext a) (r - 1 - j) + ∑ i ∈ Ico (r - 1 - j) r, ext a i := by
    unfold wsum
    rw [Finset.sum_range_add_sum_Ico _ (by omega)]
  rw [h1, h2]; omega

/-- **Reversal:** `F_r(a) ≡ X_r(a ∘ rev) (mod 3^r)`. -/
theorem Xmod_rev {r : ℕ} (a : Fin r → ℕ) : Xmod (a ∘ Fin.rev) = Fres (ext a) r := by
  rw [Xmod_eq_sum, Fres_eq_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  rw [wsum_ext_rev a (show r - 1 - j < r by omega), show r - 1 - (r - 1 - j) = j by omega]

lemma rev_mem_words {r S : ℕ} {a : Fin r → ℕ} (ha : a ∈ words r S) : a ∘ Fin.rev ∈ words r S := by
  rw [mem_words] at ha ⊢
  refine ⟨?_, fun i => ha.2 _⟩
  rw [← ha.1]
  exact Equiv.sum_comp Fin.revPerm a

/-- **Word sums are invariant under reversal**, so the source-order residue has the same joint
law with `S` as the target-outward residue. -/
theorem sum_words_rev {β : Type*} [AddCommMonoid β] (r S : ℕ) (f : ZMod (3 ^ r) → β) :
    ∑ a ∈ words r S, f (Fres (ext a) r) = ∑ a ∈ words r S, f (Xmod a) := by
  refine Finset.sum_nbij' (fun a => a ∘ Fin.rev) (fun a => a ∘ Fin.rev)
    (fun a ha => rev_mem_words ha) (fun a ha => rev_mem_words ha)
    (fun a _ => by ext i; simp) (fun a _ => by ext i; simp) (fun a _ => ?_)
  rw [Xmod_rev]

/-! ## Truncation -/

lemma cast_half {m n : ℕ} (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m))) (half n) = half m := by
  set φ := ZMod.castHom (pow_dvd_pow 3 h) (ZMod (3 ^ m))
  have h2 : φ 2 * φ (half n) = 1 := by rw [← map_mul, two_mul_half, map_one]
  have h2' : (2 : ZMod (3 ^ m)) * φ (half n) = 1 := by rwa [map_ofNat] at h2
  calc φ (half n) = half m * (2 * φ (half n)) := by
        rw [← mul_assoc, mul_comm (half m), two_mul_half, one_mul]
    _ = half m := by rw [h2', mul_one]

lemma ext_append_left {m t : ℕ} (a1 : Fin m → ℕ) (a2 : Fin t → ℕ) {i : ℕ} (hi : i < m) :
    ext (Fin.append a1 a2) i = ext a1 i := by
  simp only [ext, hi, ↓reduceDIte, show i < m + t by omega]
  exact Fin.append_left a1 a2 ⟨i, hi⟩

/-- **Truncation:** `X_{m+t}(a₁ ++ a₂) ≡ X_m(a₁) (mod 3^m)`. -/
theorem cast_Xmod_append {m t : ℕ} (a1 : Fin m → ℕ) (a2 : Fin t → ℕ) :
    (ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right m t)) (ZMod (3 ^ m)))
      (Xmod (Fin.append a1 a2)) = Xmod a1 := by
  set φ := ZMod.castHom (pow_dvd_pow 3 (Nat.le_add_right m t)) (ZMod (3 ^ m))
  rw [Xmod_eq_sum, Xmod_eq_sum, map_sum, Finset.sum_range_add, add_comm]
  rw [Finset.sum_eq_zero (fun j _ => by rw [map_mul, map_pow, map_pow, cast_half
    (Nat.le_add_right m t), show φ 3 = 3 from map_ofNat φ 3, three_pow_eq_zero (by omega),
    zero_mul]), zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  rw [map_mul, map_pow, map_pow, cast_half (Nat.le_add_right m t),
    show φ 3 = 3 from map_ofNat φ 3]
  congr 2
  unfold wsum
  exact Finset.sum_congr rfl fun i hi => ext_append_left a1 a2 (by have := mem_range.mp hi; omega)

end CollatzCLT
