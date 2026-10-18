import LeanClt.Positivity.Words
import LeanClt.Elementary.Inverse

/-!
# Lemma 8.2: realisability, and the integer side of concatenation

**Lemma 8.2 [`lem:realisable`].** If `R` is a positive odd integer and `R ≡ F_w(z) (mod 3^{t+d})`
for some `z mod 3^t`, then `Φ_w(R)` is a positive odd integer with residue `z` mod `3^t`, its
forward valuation word is `w^rev`, and `U^d(Φ_w(R)) = R`. This is Lemma 2.1 [`lem:inverse`]
(`source_exists`) for the reversed word: a word listed from the target outwards is read from the
source as `w.reverse`, and its forward offset `F_d(w^rev)` is `ϑ_w` (`offset_rev`).

The paper's last clause (the source residue and the intermediate targets are units) is not
formalized. The paper uses it only in §8.3, to see that `Z_n` vanishes on non-units and to pick a
unit class `y_*`; the Lean route takes any residue where `Z_{n⋆}` is at least its mean, and
Lemma 8.7 is proved for every residue class, so the clause is not needed.

Integer side of §8, used for histories and for the final count:
* `realizes_iff_int`: `R ≡ ϑ_w (mod 3^d)` iff `Φ_w(R) ∈ ℤ`;
* `realizes_append`, `src_append`: a concatenation is realisable iff its pieces are, one after the
  other, and `Φ_{u++v} = Φ_v ∘ Φ_u` on the sources;
* `realizes_reduce`, `src_reduce`: lowering the outermost letter by `2j` keeps realisability (because
  `3 ∣ 4^j - 1`), and the original source is `Ψ_j(x) = 4^j x + (4^j - 1)/3`;
* `depth_unique`, `word_unique`: a source reaches a `U`-nonperiodic target at one depth only, and
  the word is then determined;
* `flatten_inj`: the cuts of a concatenation of blocks from prefix-free families are determined by
  the concatenated word.
-/

open Finset Function

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## The source-order word of a target-outward word -/

lemma getD_reverse_cons_lt (b : ℕ) (w : Word) {i : ℕ} (hi : i < w.length) :
    (b :: w).reverse.getD i 1 = w.reverse.getD i 1 := by
  rw [List.reverse_cons, List.getD_append _ _ _ _ (by simpa using hi)]

lemma getD_reverse_cons_len (b : ℕ) (w : Word) : (b :: w).reverse.getD w.length 1 = b := by
  rw [List.reverse_cons, List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma pos_rev {w : Word} (hw : w.Pos) (i : ℕ) : 1 ≤ w.reverse.getD i 1 := by
  by_cases h : i < w.reverse.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.mem_reverse.mp (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]

/-- The total of the source-order word is `A(w)`. -/
lemma wsum_rev (w : Word) : wsum (fun i => w.reverse.getD i 1) w.length = tot w := by
  induction w with
  | nil => simp [wsum]
  | cons b w ih =>
    rw [List.length_cons, wsum, Finset.sum_range_succ, ← wsum,
      wsum_congr (b := fun i => w.reverse.getD i 1) (fun i hi => getD_reverse_cons_lt b w hi),
      ih, getD_reverse_cons_len, tot_cons, add_comm]

/-- The forward offset of the reversed word is `ϑ_w`: `F_d(w^rev) = ϑ_w`. -/
lemma offset_rev (w : Word) : offset (fun i => w.reverse.getD i 1) w.length = thetaW w := by
  induction w with
  | nil => simp [offset, thetaW_nil]
  | cons b w ih =>
    rw [List.length_cons, offset,
      offset_congr (b := fun i => w.reverse.getD i 1) (fun i hi => getD_reverse_cons_lt b w hi),
      ih, getD_reverse_cons_len, thetaW_cons, add_comm]

/-! ## Integrality -/

/-- `2^{A(w)} ϑ_w`, a natural number. -/
def kint (w : Word) : ℕ := ∑ j ∈ range w.length, 3 ^ j * 2 ^ (tot w - pre w (j + 1))

lemma pre_le_tot (w : Word) (k : ℕ) : pre w k ≤ tot w := by
  unfold pre tot
  have := List.sum_take_add_sum_drop w k
  omega

lemma kint_cast (w : Word) : (kint w : ℚ) = 2 ^ tot w * thetaW w := by
  unfold kint thetaW
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_sub₀ _ (by norm_num) (pre_le_tot w _)]
  field_simp

lemma thetaRes_eq_kint (n : ℕ) (w : Word) :
    thetaRes n w = (kint w : ZMod (3 ^ n)) * half n ^ tot w := by
  unfold kint thetaRes
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le (pre_le_tot w (j + 1))
  rw [hc, Nat.add_sub_cancel_left, pow_add]
  have := two_pow_mul_half_pow n c
  linear_combination (-(3 : ZMod (3 ^ n)) ^ j * half n ^ pre w (j + 1)) * this

/-- `R ≡ ϑ_w (mod 3^d)` iff `Φ_w(R)` is an integer. -/
theorem realizes_iff_int (w : Word) (R : ℕ) : Realizes w R ↔ ∃ N : ℤ, Phi w R = N := by
  have hK := kint_cast w
  have h3 : (3 : ℚ) ^ w.length ≠ 0 := by positivity
  constructor
  · intro h
    unfold Realizes at h
    rw [thetaRes_eq_kint] at h
    have h2 : ((2 ^ tot w * R - kint w : ℤ) : ZMod (3 ^ w.length)) = 0 := by
      push_cast
      rw [h]
      have := two_pow_mul_half_pow w.length (tot w)
      linear_combination (kint w : ZMod (3 ^ w.length)) * this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    obtain ⟨N, hN⟩ := h2
    refine ⟨N, ?_⟩
    have hN' : ((2 : ℚ) ^ tot w * R - kint w) = 3 ^ w.length * N := by exact_mod_cast hN
    unfold Phi
    rw [hK] at hN'
    field_simp
    linear_combination hN'
  · rintro ⟨N, hN⟩
    unfold Phi at hN
    have hN' : (((2 ^ tot w * R - kint w : ℤ)) : ℚ) = ((3 ^ w.length * N : ℤ) : ℚ) := by
      push_cast
      rw [hK]
      field_simp at hN
      linear_combination hN
    have hZ : ((2 ^ tot w * R - kint w : ℤ) : ZMod (3 ^ w.length)) =
        ((3 ^ w.length * N : ℤ) : ZMod (3 ^ w.length)) := by
      rw [Int.cast_inj.mp hN']
    push_cast at hZ
    have h0 : (3 : ZMod (3 ^ w.length)) ^ w.length = 0 := by
      exact_mod_cast ZMod.natCast_self (3 ^ w.length)
    rw [h0, zero_mul] at hZ
    unfold Realizes
    rw [thetaRes_eq_kint]
    have := two_pow_mul_half_pow w.length (tot w)
    linear_combination (half w.length ^ tot w) * hZ - (R : ZMod (3 ^ w.length)) * this

/-- **Lemma 8.2, core:** a realisable word has a positive odd source `src w R = Φ_w(R)`, whose
forward valuation word is `w^rev`, and `U^d(src w R) = R`. -/
theorem realisable_of_realizes {w : Word} (hw : w.Pos) {R : ℕ} (hR : Odd R) (h : Realizes w R) :
    (src w R : ℚ) = Phi w R ∧ Odd (src w R) ∧
      (∀ i < w.length, vword (src w R) i = w.reverse.getD i 1) ∧
      U^[w.length] (src w R) = R := by
  obtain ⟨N, hN⟩ := (realizes_iff_int w R).mp h
  obtain ⟨n, hnN, hodd, hword, hU⟩ :=
    source_exists (a := fun i => w.reverse.getD i 1) (pos_rev hw) (r := w.length) hR (N := N)
      (by rw [wsum_rev, offset_rev]; exact hN.symm)
  have hNn : (N : ℚ) = n := by rw [← hnN]; push_cast; rfl
  have hsrc : src w R = n := by
    unfold src; rw [hN, hNn]; exact Nat.floor_natCast n
  rw [hsrc]
  exact ⟨by rw [hN, hNn], hodd, hword, hU⟩

/-! ## Reduction to a smaller modulus -/

lemma cast_thetaRes {m n : ℕ} (h : m ≤ n) (w : Word) :
    (ZMod.cast (thetaRes n w) : ZMod (3 ^ m)) = thetaRes m w := by
  rw [thetaRes_eq_XmodN, thetaRes_eq_XmodN, cast_XmodN h]

lemma cast_FwN {m n : ℕ} (h : m ≤ n) (w : Word) {t : ℕ} (z : ZMod (3 ^ t)) :
    (ZMod.cast (FwN n w z) : ZMod (3 ^ m)) = FwN m w z := by
  have hc := cast_thetaRes h w
  rw [← ZMod.castHom_apply (h := pow_dvd_pow 3 h)] at hc ⊢
  unfold FwN
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_ofNat, cast_half h, hc]

/-- If `3^d a ≡ 3^d b (mod 3^{t+d})` then `a ≡ b (mod 3^t)`. -/
lemma cast_eq_of_three_pow_mul {d t : ℕ} {a b : ℤ}
    (h : ((3 ^ d * a : ℤ) : ZMod (3 ^ (t + d))) = ((3 ^ d * b : ℤ) : ZMod (3 ^ (t + d)))) :
    (a : ZMod (3 ^ t)) = (b : ZMod (3 ^ t)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h ⊢
  push_cast at h ⊢
  rw [← mul_sub, pow_add, mul_comm ((3 : ℤ) ^ t)] at h
  exact (mul_dvd_mul_iff_left (by positivity : (3 : ℤ) ^ d ≠ 0)).mp h

/-- **Lemma 8.2 [`lem:realisable`].** -/
theorem realisable {w : Word} (hw : w.Pos) {R t : ℕ} (hR : Odd R) {z : ZMod (3 ^ t)}
    (hz : (R : ZMod (3 ^ (t + w.length))) = Fw t w z) :
    Realizes w R ∧ (src w R : ℚ) = Phi w R ∧ Odd (src w R) ∧ ((src w R : ℕ) : ZMod (3 ^ t)) = z ∧
      (∀ i < w.length, vword (src w R) i = w.reverse.getD i 1) ∧
      U^[w.length] (src w R) = R := by
  -- realisability: reduce the congruence modulo `3^d`
  have hreal : Realizes w R := by
    have := congrArg (ZMod.cast : ZMod (3 ^ (t + w.length)) → ZMod (3 ^ w.length)) hz
    rw [ZMod.cast_natCast (pow_dvd_pow 3 (Nat.le_add_left _ _)), Fw,
      cast_FwN (Nat.le_add_left _ _)] at this
    unfold Realizes
    rw [this, FwN]
    have h0 : (3 : ZMod (3 ^ w.length)) ^ w.length = 0 := by
      exact_mod_cast ZMod.natCast_self (3 ^ w.length)
    rw [h0]; ring
  obtain ⟨hsrc, hodd, hword, hU⟩ := realisable_of_realizes hw hR hreal
  refine ⟨hreal, hsrc, hodd, ?_, hword, hU⟩
  -- the residue: `3^d · src = 2^A R - K ≡ 3^d z (mod 3^{t+d})`
  have hK := kint_cast w
  have hint : ((3 ^ w.length * (src w R : ℤ) : ℤ) : ℚ) = ((2 ^ tot w * R - kint w : ℤ) : ℚ) := by
    push_cast
    rw [hsrc, hK]
    unfold Phi
    field_simp
  have hZ := congrArg (Int.cast : ℤ → ZMod (3 ^ (t + w.length))) (Int.cast_inj.mp hint)
  have hR' : ((2 ^ tot w * R - kint w : ℤ) : ZMod (3 ^ (t + w.length))) =
      ((3 ^ w.length * (z.val : ℤ) : ℤ) : ZMod (3 ^ (t + w.length))) := by
    push_cast
    rw [hz, Fw, FwN, thetaRes_eq_kint]
    have := two_pow_mul_half_pow (t + w.length) (tot w)
    linear_combination ((3 : ZMod (3 ^ (t + w.length))) ^ w.length * ((z.val : ℕ) :
      ZMod (3 ^ (t + w.length))) + (kint w : ZMod (3 ^ (t + w.length)))) * this
  have := cast_eq_of_three_pow_mul (hZ.trans hR')
  push_cast at this
  rw [this, ZMod.natCast_zmod_val]

/-! ## Concatenation on the integer side -/

/-- `ℤ[1/2] ∩ ℤ[1/3] = ℤ`: if `2^k q` and `3^d q` are integers, so is `q`. -/
lemma rat_int_of_two_pow_three_pow {q : ℚ} {k d : ℕ} {A B : ℤ}
    (hA : 2 ^ k * q = A) (hB : 3 ^ d * q = B) : ∃ z : ℤ, q = z := by
  have hAB : (3 : ℤ) ^ d * A = 2 ^ k * B := by
    have : (3 : ℚ) ^ d * A = 2 ^ k * B := by rw [← hA, ← hB]; ring
    exact_mod_cast this
  have hcop : IsCoprime ((2 : ℤ) ^ k) (3 ^ d) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have hdvd : (2 : ℤ) ^ k ∣ A := hcop.dvd_of_dvd_mul_left ⟨B, by rw [← hAB]⟩
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, mul_left_cancel₀ (pow_ne_zero k (two_ne_zero : (2 : ℚ) ≠ 0)) ?_⟩
  rw [hA, hz]; push_cast; ring

/-- `3^d Φ_w(R)` is an integer. -/
lemma three_pow_mul_Phi (w : Word) (R : ℕ) :
    (3 : ℚ) ^ w.length * Phi w R = ((2 ^ tot w * R - kint w : ℤ) : ℚ) := by
  push_cast
  rw [kint_cast]
  unfold Phi
  field_simp

/-- **Realisability of a concatenation**, piece by piece (`u` nearest the target). -/
theorem realizes_append {u v : Word} (hu : u.Pos) {M : ℕ} (hM : Odd M) :
    Realizes (u ++ v) M ↔ Realizes u M ∧ Realizes v (src u M) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (realizes_iff_int _ _).mp h
    rw [Phi_append] at hN
    -- `Φ_u(M)` lies in `ℤ[1/3]` and, by `Φ_v(Φ_u(M)) ∈ ℤ`, in `ℤ[1/2]`
    have hA : (2 : ℚ) ^ tot v * Phi u M = ((3 ^ v.length * N + kint v : ℤ) : ℚ) := by
      push_cast
      rw [kint_cast]
      unfold Phi at hN ⊢
      field_simp at hN ⊢
      linear_combination hN
    obtain ⟨N1, hN1⟩ := rat_int_of_two_pow_three_pow hA (three_pow_mul_Phi u M)
    have hu' : Realizes u M := (realizes_iff_int u M).mpr ⟨N1, hN1⟩
    refine ⟨hu', (realizes_iff_int v _).mpr ⟨N, ?_⟩⟩
    rw [(realisable_of_realizes hu hM hu').1, hN]
  · rintro ⟨hu', hv'⟩
    obtain ⟨N, hN⟩ := (realizes_iff_int v _).mp hv'
    refine (realizes_iff_int _ _).mpr ⟨N, ?_⟩
    rw [Phi_append, ← (realisable_of_realizes hu hM hu').1, hN]

/-- **Sources compose:** `src (u ++ v) M = src v (src u M)`. -/
theorem src_append {u v : Word} (hu : u.Pos) (hv : v.Pos) {M : ℕ} (hM : Odd M)
    (h : Realizes (u ++ v) M) : src (u ++ v) M = src v (src u M) := by
  have huv : (u ++ v).Pos := fun a ha => by
    rcases List.mem_append.mp ha with ha | ha
    · exact hu a ha
    · exact hv a ha
  obtain ⟨hu', hv'⟩ := (realizes_append hu hM).mp h
  have h1 := (realisable_of_realizes huv hM h).1
  have hsu := realisable_of_realizes hu hM hu'
  have h2 := (realisable_of_realizes hv hsu.2.1 hv').1
  have : (src (u ++ v) M : ℚ) = (src v (src u M) : ℚ) := by
    rw [h1, Phi_append, ← hsu.1, h2]
  exact_mod_cast this

/-! ## The terminal reduction `Ψ_j` -/

lemma thetaRes_single (n b : ℕ) : thetaRes n [b] = half n ^ b := by
  rw [thetaRes_cons, thetaRes_nil]; ring

lemma Phi_single (b : ℕ) (x : ℚ) : Phi [b] x = (2 ^ b * x - 1) / 3 := by
  unfold Phi
  rw [thetaW_cons, thetaW_nil]
  simp only [tot, List.sum_cons, List.sum_nil, add_zero, List.length_singleton, pow_one]
  field_simp
  ring

lemma realizes_iff_of_length {w : Word} {n : ℕ} (hn : w.length = n) (R : ℕ) :
    Realizes w R ↔ (R : ZMod (3 ^ n)) = thetaRes n w := by
  subst hn; rfl

/-- **Lowering the outermost letter by `2j` keeps realisability**, because `3 ∣ 4^j - 1`. -/
theorem realizes_reduce (w : Word) (a j R : ℕ) :
    Realizes (w ++ [a + 2 * j]) R ↔ Realizes (w ++ [a]) R := by
  rw [realizes_iff_of_length (n := w.length + 1) (by simp),
    realizes_iff_of_length (n := w.length + 1) (by simp), thetaRes_append, thetaRes_append,
    thetaRes_single, thetaRes_single]
  have hdiff : (3 : ZMod (3 ^ (w.length + 1))) ^ w.length * half (w.length + 1) ^ tot w *
      half (w.length + 1) ^ (a + 2 * j) =
      3 ^ w.length * half (w.length + 1) ^ tot w * half (w.length + 1) ^ a := by
    -- `half² - 1 = -3 half²`, so `3^d (half^{2j} - 1) = -3^{d+1}(…) = 0`
    have h4 : (2 : ZMod (3 ^ (w.length + 1))) ^ 2 * half (w.length + 1) ^ 2 = 1 :=
      two_pow_mul_half_pow _ 2
    have hgeom := geom_sum_mul (half (w.length + 1) ^ 2) j
    have h0 : (3 : ZMod (3 ^ (w.length + 1))) ^ (w.length + 1) = 0 := by
      exact_mod_cast ZMod.natCast_self (3 ^ (w.length + 1))
    rw [pow_add (half (w.length + 1)) a (2 * j), pow_mul (half (w.length + 1)) 2 j]
    linear_combination
      (-(half (w.length + 1) ^ tot w * half (w.length + 1) ^ a *
        (∑ i ∈ range j, (half (w.length + 1) ^ 2) ^ i) * half (w.length + 1) ^ 2)) * h0 +
      (3 ^ w.length * half (w.length + 1) ^ tot w * half (w.length + 1) ^ a *
        (∑ i ∈ range j, (half (w.length + 1) ^ 2) ^ i)) * h4 +
      (-(3 : ZMod (3 ^ (w.length + 1))) ^ w.length * half (w.length + 1) ^ tot w *
        half (w.length + 1) ^ a) * hgeom
  rw [hdiff]

lemma three_dvd_four_pow_sub_one (j : ℕ) : 3 ∣ 4 ^ j - 1 := by
  have : 4 ^ j ≡ 1 ^ j [MOD 3] := Nat.ModEq.pow j (by decide)
  rw [one_pow] at this
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp this.symm

/-- **The reduction `Ψ_j`:** the source of the word with outermost letter `a + 2j` is
`4^j x + (4^j - 1)/3`, where `x` is the source of the word with outermost letter `a`. -/
theorem src_reduce {w : Word} (hw : w.Pos) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) {R : ℕ} (hR : Odd R)
    (h : Realizes (w ++ [a]) R) :
    src (w ++ [a + 2 * j]) R = 4 ^ j * src (w ++ [a]) R + (4 ^ j - 1) / 3 := by
  have hpa : (w ++ [a]).Pos := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hw x hx
    · rw [List.mem_singleton.mp hx]; exact ha
  have hpb : (w ++ [a + 2 * j]).Pos := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hw x hx
    · rw [List.mem_singleton.mp hx]; omega
  have h' := (realizes_reduce w a j R).mpr h
  have e1 := (realisable_of_realizes hpb hR h').1
  have e2 := (realisable_of_realizes hpa hR h).1
  have hc : (((4 ^ j - 1) / 3 : ℕ) : ℚ) = (4 ^ j - 1) / 3 := by
    rw [Nat.cast_div (three_dvd_four_pow_sub_one j) (by norm_num),
      Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast; ring
  have : (src (w ++ [a + 2 * j]) R : ℚ) = 4 ^ j * src (w ++ [a]) R + (4 ^ j - 1) / 3 := by
    rw [e1, e2, Phi_append, Phi_append, Phi_single, Phi_single, pow_add, pow_mul]
    ring
  rw [← hc] at this
  exact_mod_cast this

/-! ## Uniqueness: depth, word and cuts -/

/-- A source reaches a `U`-nonperiodic target at one depth only. -/
lemma depth_unique {M x d d' : ℕ} (hM : ∀ p, 0 < p → U^[p] M ≠ M) (h : U^[d] x = M)
    (h' : U^[d'] x = M) : d = d' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · apply hM (d' - d) (by omega)
    conv_lhs => rw [← h]
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le, h']
  · apply hM (d - d') (by omega)
    conv_lhs => rw [← h']
    rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le, h]

/-- **A source determines the word** that takes it to a `U`-nonperiodic target. -/
theorem word_unique {M : ℕ} (hMo : Odd M) (hM : ∀ p, 0 < p → U^[p] M ≠ M) {w w' : Word}
    (hw : w.Pos) (hw' : w'.Pos) (h : Realizes w M) (h' : Realizes w' M)
    (hx : src w M = src w' M) : w = w' := by
  obtain ⟨-, -, hv, hU⟩ := realisable_of_realizes hw hMo h
  obtain ⟨-, -, hv', hU'⟩ := realisable_of_realizes hw' hMo h'
  rw [hx] at hv hU
  have hlen : w.length = w'.length := depth_unique hM hU hU'
  apply List.reverse_injective
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have hi : i < w.length := by simpa using h1
  have e := (hv i hi).symm.trans (hv' i (by omega))
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e

/-- **The cuts are determined by the word:** blocks from prefix-free families, concatenated. -/
theorem flatten_inj {V : ℕ → Finset Word} (hV : ∀ j, PrefixFree (V j)) :
    ∀ (H H' : List Word), H.length = H'.length →
      (∀ j (h : j < H.length), H[j] ∈ V j) → (∀ j (h : j < H'.length), H'[j] ∈ V j) →
      H.flatten = H'.flatten → H = H' := by
  intro H
  induction H generalizing V with
  | nil => intro H' hl _ _ _; exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | cons w H ih =>
    intro H' hl hH hH' hf
    obtain ⟨w', H₁', rfl⟩ := List.exists_cons_of_length_pos (by simp at hl; omega : 0 < H'.length)
    rw [List.flatten_cons, List.flatten_cons] at hf
    have hw := hH 0 (by simp)
    have hw' := hH' 0 (by simp)
    simp only [List.getElem_cons_zero] at hw hw'
    have p1 : w <+: w' ++ H₁'.flatten := hf ▸ List.prefix_append w H.flatten
    have p2 : w' <+: w' ++ H₁'.flatten := List.prefix_append _ _
    have hww' : w = w' := by
      rcases le_total w.length w'.length with hle | hle
      · exact hV 0 w hw w' hw' (List.prefix_of_prefix_length_le p1 p2 hle)
      · exact (hV 0 w' hw' w hw (List.prefix_of_prefix_length_le p2 p1 hle)).symm
    subst hww'
    rw [ih (V := fun j => V (j + 1)) (fun j => hV (j + 1)) H₁' (by simpa using hl)
      (fun j h => by
        have := hH (j + 1) (by simp; omega)
        rwa [List.getElem_cons_succ] at this)
      (fun j h => by
        have := hH' (j + 1) (by simp; omega)
        rwa [List.getElem_cons_succ] at this)
      (List.append_cancel_left hf)]

end Positivity
end CollatzCLT
