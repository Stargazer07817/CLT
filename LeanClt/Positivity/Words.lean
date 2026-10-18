import LeanClt.Mixing.Marginal

/-!
# §8: words listed from the target outwards

Section 8 lists words **from the target outwards**: `w = (a₁, …, a_d)`, `a₁` nearest the target. A
word is a `List ℕ` in that order. Notation of §8:

* `tot w = A(w) = ∑ aᵢ`, `pre w j = A_j = a₁ + ⋯ + a_j`;
* `gm w = 2^{-A(w)}` (its geometric probability), `wt w = W(w) = 3^d 2^{-A(w)}`;
* `thetaW w = ϑ_w = ∑_{j=1}^d 3^{j-1} 2^{-A_j} ∈ ℤ[1/2]` and `thetaRes n w = ϑ_w mod 3^n`;
* `Phi w R = Φ_w(R) = 2^{A(w)} (R - ϑ_w)/3^d`, the inverse of the forward map `x ↦ W x + ϑ_w` of
  the reversed word; `src w R = ⌊Φ_w(R)⌋₊`; `Realizes w R`: `R ≡ ϑ_w (mod 3^d)`;
* `PrefixFree V`, `pmass V = p(V) = ∑_{w ∈ V} 2^{-A(w)}`;
* `FwN n w z = 3^d 2^{-A(w)} z + ϑ_w mod 3^n` for `z mod 3^t`, and `Fw t w = FwN (t + d) w`, the
  injection `F_w : G_t → G_{t+d}` of §8.1.

Concatenation is target-outward: `u ++ v` applies `u` nearest the target, so
`ϑ_{u++v} = ϑ_u + 3^{|u|} 2^{-A(u)} ϑ_v` (`thetaW_append`, `thetaRes_append`) and
`Φ_{u++v} = Φ_v ∘ Φ_u` (`Phi_append`).

## The prefix decomposition of the offset law

`lawXpre n w y = P(X_n = y, the first |w| letters are w)` under `Geom(2)^n`. The main result,
`lawXpre_decomp`, is the identity behind `T_w ρ_t` as a sub-distribution of `ρ_{t+d}` in the
proof of Lemma 8.3 [`lem:B2`]:

  `P(X_{d+t} = y, prefix = w) = 2^{-A(w)} P(F_w(X_t) = y)`,

which follows from `X̃_{d+t}(w ++ v) = ϑ_w + 3^d 2^{-A(w)} X̃_t(v)` (`XmodN_append`). For a
prefix-free family the prefix events are disjoint (`sum_lawXpre_le`), each has mass `2^{-A(w)}`
(`sum_lawXpre`), and hence `p(V) ≤ 1` (`pmass_le_one`, the geometric Kraft inequality).
-/

open Finset

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Definitions -/

/-- A word `(a₁, …, a_d)`, listed from the target outwards (§8). -/
abbrev Word := List ℕ

/-- All letters are `≥ 1`. -/
def Word.Pos (w : Word) : Prop := ∀ a ∈ w, 1 ≤ a

/-- `A(w)`, the total of a word. -/
def tot (w : Word) : ℕ := w.sum

/-- `A_j`, the `j`-th partial sum (target outwards). -/
def pre (w : Word) (j : ℕ) : ℕ := (w.take j).sum

/-- `2^{-A(w)}`, the geometric probability of a word. -/
def gm (w : Word) : ℝ := (1 / 2 : ℝ) ^ tot w

/-- `W(w) = 3^d 2^{-A(w)}`, the weight of a word. -/
def wt (w : Word) : ℝ := 3 ^ w.length * gm w

/-- `ϑ_w = ∑_{j=1}^d 3^{j-1} 2^{-A_j}`. -/
def thetaW (w : Word) : ℚ := ∑ j ∈ range w.length, (3 : ℚ) ^ j / 2 ^ pre w (j + 1)

/-- `ϑ_w mod 3^n`. -/
def thetaRes (n : ℕ) (w : Word) : ZMod (3 ^ n) :=
  ∑ j ∈ range w.length, (3 : ZMod (3 ^ n)) ^ j * half n ^ pre w (j + 1)

/-- `w` is realisable at the target `R`: `R ≡ ϑ_w (mod 3^d)`. -/
def Realizes (w : Word) (R : ℕ) : Prop := (R : ZMod (3 ^ w.length)) = thetaRes w.length w

/-- `Φ_w(R) = 2^{A(w)} (R - ϑ_w)/3^d`. -/
def Phi (w : Word) (R : ℚ) : ℚ := 2 ^ tot w * (R - thetaW w) / 3 ^ w.length

/-- `Φ_w(R)` as a natural number (meaningful when `Realizes w R`). -/
def src (w : Word) (R : ℕ) : ℕ := ⌊Phi w R⌋₊

/-- A prefix-free family of words. -/
def PrefixFree (V : Finset Word) : Prop := ∀ v ∈ V, ∀ w ∈ V, v <+: w → v = w

/-- `p(V) = ∑_{w ∈ V} 2^{-A(w)}`. -/
def pmass (V : Finset Word) : ℝ := ∑ w ∈ V, gm w

/-- `z ↦ 3^d 2^{-A(w)} z + ϑ_w`, from residues mod `3^t` to residues mod `3^n` (`z` is lifted by
its least nonnegative representative). -/
def FwN (n : ℕ) {t : ℕ} (w : Word) (z : ZMod (3 ^ t)) : ZMod (3 ^ n) :=
  (3 : ZMod (3 ^ n)) ^ w.length * half n ^ tot w * ((z.val : ℕ) : ZMod (3 ^ n)) + thetaRes n w

/-- `F_w : G_t → G_{t+d}` of §8.1. -/
def Fw (t : ℕ) (w : Word) (z : ZMod (3 ^ t)) : ZMod (3 ^ (t + w.length)) :=
  FwN (t + w.length) w z

open Classical in
/-- `P(X_n = y, the first |w| letters are w)` under `Geom(2)^n`. -/
def lawXpre (n : ℕ) (w : Word) (y : ZMod (3 ^ n)) : ℝ :=
  ∑' s : ℕ, ∑ a ∈ words n s, if Xmod a = y ∧ w <+: List.ofFn a then (1 / 2 : ℝ) ^ s else 0

/-! ## Totals, weights and offsets under concatenation -/

@[simp] lemma tot_nil : tot [] = 0 := rfl

lemma tot_cons (a : ℕ) (w : Word) : tot (a :: w) = a + tot w := List.sum_cons

lemma tot_append (u v : Word) : tot (u ++ v) = tot u + tot v := List.sum_append

lemma pre_zero (w : Word) : pre w 0 = 0 := by simp [pre]

lemma pre_cons_succ (a : ℕ) (w : Word) (j : ℕ) : pre (a :: w) (j + 1) = a + pre w j := by
  simp [pre]

lemma pre_length (w : Word) : pre w w.length = tot w := by simp [pre, tot]

lemma pre_eq_sum (w : Word) {k : ℕ} (hk : k ≤ w.length) :
    pre w k = ∑ i ∈ range k, w.getD i 0 := by
  induction k with
  | zero => simp [pre]
  | succ k ih =>
    unfold pre
    rw [List.sum_take_succ w k (by omega), Finset.sum_range_succ, ← ih (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    rfl

lemma gm_pos (w : Word) : 0 < gm w := by unfold gm; positivity

lemma wt_pos (w : Word) : 0 < wt w := by unfold wt; have := gm_pos w; positivity

lemma gm_append (u v : Word) : gm (u ++ v) = gm u * gm v := by
  simp [gm, tot_append, pow_add]

lemma wt_append (u v : Word) : wt (u ++ v) = wt u * wt v := by
  simp only [wt, gm_append, List.length_append, pow_add]; ring

lemma thetaW_nil : thetaW [] = 0 := by simp [thetaW]

lemma thetaW_cons (a : ℕ) (w : Word) : thetaW (a :: w) = (1 + 3 * thetaW w) / 2 ^ a := by
  unfold thetaW
  rw [List.length_cons, Finset.sum_range_succ']
  have h0 : pre (a :: w) (0 + 1) = a := by simp [pre]
  rw [h0]
  simp_rw [pre_cons_succ]
  rw [Finset.mul_sum, add_div, Finset.sum_div, add_comm (1 / 2 ^ a : ℚ)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, pow_succ]; field_simp; ring

lemma thetaRes_nil (n : ℕ) : thetaRes n [] = 0 := by simp [thetaRes]

lemma thetaRes_cons (n a : ℕ) (w : Word) :
    thetaRes n (a :: w) = half n ^ a * (1 + 3 * thetaRes n w) := by
  unfold thetaRes
  rw [List.length_cons, Finset.sum_range_succ']
  have h0 : pre (a :: w) (0 + 1) = a := by simp [pre]
  rw [h0]
  simp_rw [pre_cons_succ]
  rw [mul_add, mul_one, Finset.mul_sum, Finset.mul_sum, add_comm (half n ^ a)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, pow_succ]; ring
  · simp

/-- **Concatenation of offsets** (target outwards): `ϑ_{u++v} = ϑ_u + 3^{|u|} 2^{-A(u)} ϑ_v`. -/
theorem thetaW_append (u v : Word) :
    thetaW (u ++ v) = thetaW u + 3 ^ u.length / 2 ^ tot u * thetaW v := by
  induction u with
  | nil => simp [thetaW_nil]
  | cons a u ih =>
    rw [List.cons_append, thetaW_cons, ih, thetaW_cons, List.length_cons, tot_cons, pow_add,
      pow_succ]
    field_simp
    ring

/-- **Concatenation of offsets mod `3^n`.** -/
theorem thetaRes_append (n : ℕ) (u v : Word) :
    thetaRes n (u ++ v) = thetaRes n u + 3 ^ u.length * half n ^ tot u * thetaRes n v := by
  induction u with
  | nil => simp [thetaRes_nil]
  | cons a u ih =>
    rw [List.cons_append, thetaRes_cons, ih, thetaRes_cons, List.length_cons, tot_cons, pow_add,
      pow_succ]
    ring

/-- `Φ_{u++v} = Φ_v ∘ Φ_u`: `u` is peeled first, nearest the target. -/
theorem Phi_append (u v : Word) (R : ℚ) : Phi (u ++ v) R = Phi v (Phi u R) := by
  unfold Phi
  rw [thetaW_append, tot_append, List.length_append, pow_add, pow_add]
  field_simp
  ring

/-! ## Bridge to the fixed-length words of §2.3 -/

lemma tot_ofFn {p : ℕ} (a : Fin p → ℕ) : tot (List.ofFn a) = ∑ i, a i := by
  simp [tot, List.sum_ofFn]

lemma tot_eq_sum_get (w : Word) : ∑ i, w.get i = tot w := by
  rw [← tot_ofFn, List.ofFn_get]

lemma pos_get {w : Word} (hw : w.Pos) (i : Fin w.length) : 1 ≤ w.get i :=
  hw _ (List.get_mem w i)

/-- The offset of a fixed-length word is the list offset: `X̃_p(a) = ϑ_{ofFn a}` at any modulus. -/
lemma thetaRes_ofFn (n : ℕ) {p : ℕ} (a : Fin p → ℕ) : thetaRes n (List.ofFn a) = XmodN n a := by
  unfold thetaRes XmodN
  rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [pre_eq_sum _ (by rw [List.length_ofFn]; exact j.isLt), psum_eq]
  unfold wsum
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < p := by have := j.isLt; rw [Finset.mem_range] at hi; omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
  simp [ext, hi]

lemma thetaRes_eq_XmodN (n : ℕ) (w : Word) : thetaRes n w = XmodN n w.get := by
  rw [← thetaRes_ofFn, List.ofFn_get]

/-- Multiplying by `3^d` kills the difference between `x mod 3^{d+t}` and the least representative
of `x mod 3^t`. -/
lemma three_pow_mul_val_cast (d t : ℕ) (x : ZMod (3 ^ (d + t))) :
    (3 : ZMod (3 ^ (d + t))) ^ d * (((ZMod.cast x : ZMod (3 ^ t)).val : ℕ) : ZMod (3 ^ (d + t))) =
      3 ^ d * x := by
  have hval : (ZMod.cast x : ZMod (3 ^ t)).val = x.val % 3 ^ t := by
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hval]
  conv_rhs => rw [← ZMod.natCast_zmod_val x, ← Nat.mod_add_div x.val (3 ^ t)]
  push_cast
  rw [mul_add, ← mul_assoc, ← pow_add]
  have : ((3 : ZMod (3 ^ (d + t))) ^ (d + t)) = 0 := by
    exact_mod_cast ZMod.natCast_self (3 ^ (d + t))
  rw [this, zero_mul, add_zero]

/-- **The concatenation identity behind §8.1:** `X̃_{d+t}(w ++ v) = F_w(X̃_t(v)) (mod 3^{d+t})`. -/
theorem Xmod_append_get (w : Word) {t : ℕ} (v : Fin t → ℕ) :
    Xmod (Fin.append w.get v) = FwN (w.length + t) w (Xmod v) := by
  rw [Xmod_eq_XmodN, XmodN_append, tot_eq_sum_get, ← thetaRes_eq_XmodN, FwN, Xmod_eq_XmodN]
  have key := three_pow_mul_val_cast w.length t (XmodN (w.length + t) v)
  rw [cast_XmodN (Nat.le_add_left t w.length)] at key
  linear_combination (-(half (w.length + t) ^ tot w)) * key

/-- `F_w` is injective from `G_t` to `G_{d+t}`. -/
theorem FwN_injective {n t : ℕ} {w : Word} (hn : n = w.length + t) :
    Function.Injective (FwN n w : ZMod (3 ^ t) → ZMod (3 ^ n)) := by
  subst hn
  intro z z' h
  unfold FwN at h
  set N := w.length + t with hN
  have h1 : (3 : ZMod (3 ^ N)) ^ w.length * half N ^ tot w *
      (((z.val : ℕ) : ZMod (3 ^ N)) - ((z'.val : ℕ) : ZMod (3 ^ N))) = 0 := by
    linear_combination h
  have h2 : (3 : ZMod (3 ^ N)) ^ w.length *
      (((z.val : ℕ) : ZMod (3 ^ N)) - ((z'.val : ℕ) : ZMod (3 ^ N))) = 0 := by
    have := two_pow_mul_half_pow N (tot w)
    linear_combination (2 : ZMod (3 ^ N)) ^ tot w * h1 +
      (-(3 : ZMod (3 ^ N)) ^ w.length *
        (((z.val : ℕ) : ZMod (3 ^ N)) - ((z'.val : ℕ) : ZMod (3 ^ N)))) * this
  have h3 : ((((3 : ℤ) ^ w.length * ((z.val : ℤ) - (z'.val : ℤ))) : ℤ) : ZMod (3 ^ N)) = 0 := by
    push_cast; exact h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  push_cast at h3
  rw [pow_add] at h3
  have h4 : (3 : ℤ) ^ t ∣ (z.val : ℤ) - z'.val :=
    (mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ w.length ≠ 0)).mp h3
  have h5 : ((z'.val : ℤ) : ZMod (3 ^ t)) = ((z.val : ℤ) : ZMod (3 ^ t)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast; exact h4
  push_cast at h5
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h5
  exact h5.symm

/-! ## The prefix decomposition -/

/-- `∑_y F(y) μ_r(S, y) = ∑_{a ∈ words r S} F(X_r(a)) 2^{-S}`. -/
lemma sum_mul_muJ (r S : ℕ) (F : ZMod (3 ^ r) → ℝ) :
    ∑ y : ZMod (3 ^ r), F y * muJ r S y = ∑ a ∈ words r S, F (Xmod a) * (1 / 2 : ℝ) ^ S := by
  unfold muJ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- For a word `u` of length `|w|`, `w` is a prefix of `u ++ v` iff `u = w`. -/
lemma prefix_append_iff (w : Word) {t : ℕ} (u : Fin w.length → ℕ) (v : Fin t → ℕ) :
    w <+: List.ofFn (Fin.append u v) ↔ u = w.get := by
  rw [List.ofFn_fin_append]
  constructor
  · intro h
    have h1 : w <+: List.ofFn u :=
      List.prefix_of_prefix_length_le h (List.prefix_append _ _) (by simp)
    have h2 : w = List.ofFn u := h1.eq_of_length (by simp)
    exact List.ofFn_inj.mp (by rw [List.ofFn_get]; exact h2.symm)
  · rintro rfl
    rw [List.ofFn_get]
    exact List.prefix_append _ _

lemma get_mem_words {w : Word} (hw : w.Pos) (s1 : ℕ) : w.get ∈ words w.length s1 ↔ s1 = tot w := by
  rw [mem_words, tot_eq_sum_get]
  constructor
  · rintro ⟨h, -⟩; exact h.symm
  · rintro rfl; exact ⟨rfl, pos_get hw⟩

open Classical in
/-- **One counter value of the prefix decomposition.** -/
lemma sum_words_prefix {w : Word} (hw : w.Pos) (t s : ℕ) (y : ZMod (3 ^ (w.length + t))) :
    (∑ a ∈ words (w.length + t) s,
        if Xmod a = y ∧ w <+: List.ofFn a then (1 / 2 : ℝ) ^ s else 0) =
      if tot w ≤ s then gm w * ∑ z : ZMod (3 ^ t),
        (if FwN (w.length + t) w z = y then muJ t (s - tot w) z else 0) else 0 := by
  rw [sum_words_append w.length t s]
  -- only the prefix `u = w` contributes
  have hu : ∀ s1, ∑ u ∈ words w.length s1, ∑ v ∈ words t (s - s1),
      (if Xmod (Fin.append u v) = y ∧ w <+: List.ofFn (Fin.append u v)
        then (1 / 2 : ℝ) ^ s else 0) =
      if s1 = tot w then ∑ v ∈ words t (s - tot w),
        (if FwN (w.length + t) w (Xmod v) = y then (1 / 2 : ℝ) ^ s else 0) else 0 := by
    intro s1
    have : ∀ u ∈ words w.length s1, ∑ v ∈ words t (s - s1),
        (if Xmod (Fin.append u v) = y ∧ w <+: List.ofFn (Fin.append u v)
          then (1 / 2 : ℝ) ^ s else 0) =
        if u = w.get then ∑ v ∈ words t (s - s1),
          (if FwN (w.length + t) w (Xmod v) = y then (1 / 2 : ℝ) ^ s else 0) else 0 := by
      intro u _
      by_cases h : u = w.get
      · subst h
        simp only [↓reduceIte]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Xmod_append_get]
        simp only [prefix_append_iff, and_true]
      · simp only [h, ↓reduceIte]
        refine Finset.sum_eq_zero fun v _ => ?_
        have : ¬ (Xmod (Fin.append u v) = y ∧ w <+: List.ofFn (Fin.append u v)) := by
          rintro ⟨-, h'⟩
          exact h ((prefix_append_iff w u v).mp h')
        simp only [this, ↓reduceIte]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    by_cases h : s1 = tot w
    · subst h
      simp only [(get_mem_words hw _).mpr rfl, ite_true]
    · have h' : w.get ∉ words w.length s1 := fun h' => h ((get_mem_words hw _).mp h')
      simp only [h', h, ite_false]
  rw [Finset.sum_congr rfl fun s1 _ => hu s1, Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_add_one_iff]
  split_ifs with hs
  · have hG : ∀ z, (if FwN (w.length + t) w z = y then muJ t (s - tot w) z else 0) =
        (if FwN (w.length + t) w z = y then (1 : ℝ) else 0) * muJ t (s - tot w) z := by
      intro z; split_ifs <;> simp
    simp_rw [hG]
    rw [sum_mul_muJ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hs' : (1 / 2 : ℝ) ^ s = (1 / 2) ^ tot w * (1 / 2) ^ (s - tot w) := by
      rw [← pow_add]; congr 1; omega
    unfold gm
    split_ifs
    · rw [hs']; ring
    · simp
  · rfl

/-- Shifting the counter by `A`. -/
lemma tsum_shift (A : ℕ) {m : ℕ → ℝ} (hm : Summable m) :
    ∑' s, (if A ≤ s then m (s - A) else 0) = ∑' s, m s := by
  set f : ℕ → ℝ := fun s => if A ≤ s then m (s - A) else 0 with hf
  have hshift : ∀ i, f (i + A) = m i := by intro i; simp [hf]
  have hfs : Summable f := (summable_nat_add_iff A).mp (by simpa [hshift] using hm)
  rw [← hfs.sum_add_tsum_nat_add A]
  have h0 : ∑ i ∈ range A, f i = 0 := Finset.sum_eq_zero fun i hi => by
    rw [Finset.mem_range] at hi
    simp [hf, show ¬ A ≤ i by omega]
  rw [h0, zero_add]
  exact tsum_congr hshift

open Classical in
lemma summable_prefix_term (n : ℕ) (w : Word) (y : ZMod (3 ^ n)) :
    Summable (fun s => ∑ a ∈ words n s,
      if Xmod a = y ∧ w <+: List.ofFn a then (1 / 2 : ℝ) ^ s else 0) := by
  refine Summable.of_nonneg_of_le (fun s => Finset.sum_nonneg fun a _ => by positivity)
    (fun s => ?_) (summable_lawS n)
  rw [← sum_words_half]
  exact Finset.sum_le_sum fun a _ => by
    split_ifs
    · exact le_rfl
    · positivity

/-- **The prefix decomposition of the offset law** (§8.1):
`P(X_{d+t} = y, prefix = w) = 2^{-A(w)} P(F_w(X_t) = y)`. Stated at a modulus `n = d + t`. -/
theorem lawXpre_decomp {n t : ℕ} {w : Word} (hn : n = w.length + t) (hw : w.Pos)
    (y : ZMod (3 ^ n)) :
    lawXpre n w y = gm w * ∑ z : ZMod (3 ^ t), if FwN n w z = y then lawX t z else 0 := by
  subst hn
  unfold lawXpre
  simp_rw [sum_words_prefix hw t _ y]
  have hm : Summable (fun s' => gm w * ∑ z : ZMod (3 ^ t),
      if FwN (w.length + t) w z = y then muJ t s' z else 0) := by
    refine Summable.mul_left _ (summable_sum fun z _ => ?_)
    by_cases h : FwN (w.length + t) w z = y
    · simp only [h, ↓reduceIte]; exact summable_muJ t z
    · simp only [h, ↓reduceIte]; exact summable_zero
  refine (tsum_shift (tot w) hm).trans ?_
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun z _ => by
    by_cases h : FwN (w.length + t) w z = y
    · simp only [h, ↓reduceIte]; exact summable_muJ t z
    · simp only [h, ↓reduceIte]; exact summable_zero)]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold lawX
  split_ifs <;> simp

/-- The offset law has total mass one. -/
lemma sum_lawX (n : ℕ) : ∑ y : ZMod (3 ^ n), lawX n y = 1 := by
  unfold lawX
  rw [← Summable.tsum_finsetSum (fun y _ => summable_muJ n y)]
  simp_rw [sum_muJ]
  exact tsum_lawS n

/-- **Each prefix event has mass `2^{-A(w)}`.** -/
theorem sum_lawXpre {n : ℕ} {w : Word} (hw : w.Pos) (hn : w.length ≤ n) :
    ∑ y : ZMod (3 ^ n), lawXpre n w y = gm w := by
  have hn' : n = w.length + (n - w.length) := by omega
  simp_rw [lawXpre_decomp hn' hw, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [sum_lawX, mul_one]

open Classical in
/-- **Disjointness of prefix events:** for a prefix-free family the prefix events are disjoint,
so their laws add up to at most the law of `X_n`. -/
theorem sum_lawXpre_le {V : Finset Word} (hV : PrefixFree V) (n : ℕ) (y : ZMod (3 ^ n)) :
    ∑ w ∈ V, lawXpre n w y ≤ lawX n y := by
  unfold lawXpre lawX
  rw [← Summable.tsum_finsetSum (fun w _ => summable_prefix_term n w y)]
  refine Summable.tsum_le_tsum (fun s => ?_)
    (summable_sum fun w _ => summable_prefix_term n w y) (summable_muJ n y)
  unfold muJ
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hy : Xmod a = y
  · simp only [hy, true_and, ↓reduceIte]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (V.filter (fun w => w <+: List.ofFn a)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro v hv w hw'
      simp only [Finset.mem_filter] at hv hw'
      rcases le_total v.length w.length with h | h
      · exact hV v hv.1 w hw'.1 (List.prefix_of_prefix_length_le hv.2 hw'.2 h)
      · exact (hV w hw'.1 v hv.1 (List.prefix_of_prefix_length_le hw'.2 hv.2 h)).symm
    calc ((V.filter (fun w => w <+: List.ofFn a)).card : ℝ) * (1 / 2) ^ s
        ≤ 1 * (1 / 2) ^ s := by gcongr; exact_mod_cast hcard
      _ = (1 / 2) ^ s := one_mul _
  · simp [hy]

/-- The total mass of the prefix events of a family of words of length at most `n` is `p(V)`. -/
theorem sum_sum_lawXpre {V : Finset Word} (hpos : ∀ w ∈ V, w.Pos) {n : ℕ}
    (hn : ∀ w ∈ V, w.length ≤ n) :
    ∑ y : ZMod (3 ^ n), ∑ w ∈ V, lawXpre n w y = pmass V := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w hw => sum_lawXpre (hpos w hw) (hn w hw)

/-- **The geometric Kraft inequality:** `p(V) ≤ 1` for a prefix-free family. -/
theorem pmass_le_one {V : Finset Word} (hV : PrefixFree V) (hpos : ∀ w ∈ V, w.Pos) :
    pmass V ≤ 1 := by
  set n := V.sup List.length
  have hle : ∀ w ∈ V, w.length ≤ n := fun w hw => Finset.le_sup (f := List.length) hw
  rw [← sum_sum_lawXpre hpos hle, ← sum_lawX n]
  exact Finset.sum_le_sum fun y _ => sum_lawXpre_le hV n y

lemma pmass_nonneg (V : Finset Word) : 0 ≤ pmass V :=
  Finset.sum_nonneg fun w _ => (gm_pos w).le

end Positivity
end CollatzCLT
