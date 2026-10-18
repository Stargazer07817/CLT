import LeanClt.Positivity.Blocks

/-!
# §8.2: histories, (8.5), (8.6) and Proposition 8.5

A **history** of `n` blocks is a list `[w₀, …, w_{n-1}]` with `w_j ∈ V_{b_j,K_j}` (`blocks b0 n`);
`w₀` is applied first, nearest the seed `M`. It is read through its flattened word
`w₀ ++ ⋯ ++ w_{n-1}` (target outwards), so `Φ_{H.flatten} = Φ_{w_{n-1}} ∘ ⋯ ∘ Φ_{w₀}` and the endpoint is
`endpt M H = src H.flatten M`. `hist b0 M n` keeps the histories whose flattened word is realisable
at `M` (point G2 of checkpoint 06: the paper's histories are implicitly realisable; by
`realizes_append` this is blockwise realisability).

* `histo b0 M n q y = 𝓗_{n,q}(y)`, the total weight of the histories whose endpoint is
  `≡ y (mod 3^q)`; `Zmark b0 M n = Z_n(M)`, the marked mass of §8.3 (used in stage 6).
* (8.6, `eq:C3`) is `history_bounds`: `W R + ϑ = M`, `0 ≤ ϑ ≤ 2^{b_0+1}`, `W ≤ 16^{b_0-b_n}`.
  The per-block facts are `block_wt_le` (`W(w) ≤ 16^{-e_b}`) and `block_theta_le` (`ϑ_w ≤ 2^b`).
* (8.5, `eq:C2`) is `phi_bounds`, for central blocks and targets `R ≥ 2^{b+1}`. The sentence after
  it ("all endpoints stay `≥ 16^{b_j}`") is `endpt_ge`, in the form `R ≥ 16^{b_n}/2`, derived from
  (8.6) and `M ≥ 16^{b_0}`.
* **Proposition 8.5 [`prop:C4`]** is `histogram_bound` (8.7) and `histogram_pairing` (8.8).

The hypothesis `M ≥ 16^{b_0}` of Proposition 8.5 is kept in the statements, as in the paper, but
the proofs do not use it (point G6 of checkpoint 06).
-/

open Finset Real

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Histories -/

/-- The `n`-block histories `[w₀, …, w_{n-1}]` with `w_j ∈ V_{b_j,K_j}`. -/
def blocks (b0 : ℕ) : ℕ → Finset (List Word)
  | 0 => {[]}
  | n + 1 => (blocks b0 n ×ˢ central (bseq b0 n) (Kseq n)).image fun p => p.1 ++ [p.2]

open Classical in
/-- The histories realisable at the seed `M`. -/
def hist (b0 M n : ℕ) : Finset (List Word) := (blocks b0 n).filter fun H => Realizes H.flatten M

/-- The endpoint `R` of a history applied to `M`. -/
def endpt (M : ℕ) (H : List Word) : ℕ := src H.flatten M

/-- `Z_n(M)`, the marked mass at generation `n` (§8.3). -/
def Zmark (b0 M n : ℕ) : ℝ := ∑ H ∈ hist b0 M n, wt H.flatten * rhoX (kseq b0 n) (endpt M H)

open Classical in
/-- `𝓗_{n,q}(y)`: the total weight of the `n`-block histories from `M` with endpoint
`≡ y (mod 3^q)`. -/
def histo (b0 M n q : ℕ) (y : ZMod (3 ^ q)) : ℝ :=
  ∑ H ∈ hist b0 M n, if ((endpt M H : ℕ) : ZMod (3 ^ q)) = y then wt H.flatten else 0

/-- `M_* = ∑_{j<n} ⌈b_j^{3/5}⌉`. -/
def Mstar (b0 n : ℕ) : ℕ := ∑ j ∈ range n, mB (bseq b0 j)

/-- `K_* = ∑_{j<n} K_j`. -/
def Kstar (n : ℕ) : ℕ := ∑ j ∈ range n, Kseq j

/-- `G = 2013/2000`. -/
def Gc : ℝ := 2013 / 2000

/-! ## Runs of blocks -/

/-- `H` is a run of central blocks at the scales `b_j, b_{j+1}, …`. -/
def BlockTail (b0 j : ℕ) (H : List Word) : Prop :=
  ∀ i (h : i < H.length), H[i] ∈ central (bseq b0 (j + i)) (Kseq (j + i))

lemma blockTail_nil (b0 j : ℕ) : BlockTail b0 j [] := fun i h => absurd h (by simp)

lemma blockTail_cons {b0 j : ℕ} {w : Word} {H : List Word} :
    BlockTail b0 j (w :: H) ↔ w ∈ central (bseq b0 j) (Kseq j) ∧ BlockTail b0 (j + 1) H := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, Nat.add_zero] at h0
    refine ⟨h0, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rwa [show j + (i + 1) = j + 1 + i by omega] at this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [show j + (i + 1) = j + 1 + i by omega]
      exact h i (by simp at hi; omega)

lemma mem_blocks {b0 n : ℕ} {H : List Word} :
    H ∈ blocks b0 n ↔ H.length = n ∧ BlockTail b0 0 H := by
  induction n generalizing H with
  | zero =>
    simp only [blocks, Finset.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, blockTail_nil b0 0⟩
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | succ n ih =>
    simp only [blocks, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨H', w, ⟨hH', hw⟩, rfl⟩
      obtain ⟨hl, ht⟩ := ih.mp hH'
      refine ⟨by simp [hl], fun i hi => ?_⟩
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge i H'.length with h | h
      · rw [List.getElem_append_left h]; exact ht i h
      · have hi' : i = H'.length := by omega
        subst hi'
        simpa [hl] using hw
    · rintro ⟨hl, ht⟩
      refine ⟨H.take n, H[n]'(by omega), ⟨ih.mpr ⟨by simp; omega, fun i hi => ?_⟩, ?_⟩, ?_⟩
      · rw [List.getElem_take]; exact ht i (by simp at hi; omega)
      · simpa using ht n (by omega)
      · have h1 : H.take (n + 1) = H := List.take_of_length_le (by omega)
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)] at h1
        simpa using h1

lemma mem_hist {b0 M n : ℕ} {H : List Word} :
    H ∈ hist b0 M n ↔ H ∈ blocks b0 n ∧ Realizes H.flatten M := by
  classical
  unfold hist
  exact Finset.mem_filter

lemma flatten_pos {b0 j : ℕ} {H : List Word} (h : BlockTail b0 j H) : Word.Pos H.flatten := by
  intro a ha
  obtain ⟨l, hl, hal⟩ := List.mem_flatten.mp ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  exact central_pos (h i hi) a hal

/-! ## One block: weight and offset -/

lemma block_len_le {b K : ℕ} (hb : 32 ≤ b) {w : Word} (hw : w ∈ central b K) :
    5 * w.length ≤ 8 * b := by
  have h1 := (central_spec hw).2.1
  have h2 := mB_le_wB hb
  unfold wB at h2
  omega

lemma thetaW_nonneg (w : Word) : 0 ≤ thetaW w := Finset.sum_nonneg fun j _ => by positivity

lemma thetaW_le_pow {w : Word} (hw : w.Pos) : thetaW w ≤ (3 / 2 : ℚ) ^ w.length - 1 := by
  rw [← offset_rev]; exact offset_le _ (pos_rev hw) _

/-- `ϑ_w ≤ (3/2)^{|w|} - 1 ≤ (3/2)^{8b/5} - 1 ≤ 2^b` for a central block at scale `b`. -/
lemma block_theta_le {b K : ℕ} (hb : 32 ≤ b) {w : Word} (hw : w ∈ central b K) :
    (thetaW w : ℝ) ≤ 2 ^ b := by
  have h1 := thetaW_le_pow (central_pos hw)
  have h5 := block_len_le hb hw
  have h2 : ((3 / 2 : ℚ) ^ w.length) ≤ 2 ^ b := by
    have h0 : (0 : ℚ) ≤ (3 / 2) ^ w.length := by positivity
    have : ((3 / 2 : ℚ) ^ w.length) ^ 5 ≤ (2 ^ b) ^ 5 := by
      rw [← pow_mul, ← pow_mul]
      calc (3 / 2 : ℚ) ^ (w.length * 5) ≤ (3 / 2) ^ (8 * b) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ = ((3 / 2) ^ 8) ^ b := by rw [pow_mul]
        _ ≤ (2 ^ 5) ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
        _ = 2 ^ (b * 5) := by rw [← pow_mul, mul_comm]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp this
  have : thetaW w ≤ 2 ^ b := by linarith
  exact_mod_cast this

lemma two_mul_three_pow_mul_le {b : ℕ} (hb : 100 ≤ b) : 2 * 3 ^ b * 16 ^ (b / 100) ≤ 4 ^ b := by
  obtain ⟨e, r, hr, rfl⟩ : ∃ e r, r < 100 ∧ b = 100 * e + r :=
    ⟨b / 100, b % 100, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod b 100).symm⟩
  have he : 1 ≤ e := by omega
  rw [show (100 * e + r) / 100 = e by omega, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 * (3 ^ 100 * 16) ^ e ≤ (4 ^ 100) ^ e := by
    calc 2 * (3 ^ 100 * 16) ^ e ≤ 2 ^ e * (3 ^ 100 * 16) ^ e :=
          Nat.mul_le_mul_right _ ((Nat.pow_one 2).symm.le.trans (Nat.pow_le_pow_right (by norm_num) he))
      _ = (2 * 3 ^ 100 * 16) ^ e := by rw [← mul_pow, mul_assoc]
      _ ≤ (4 ^ 100) ^ e := Nat.pow_le_pow_left (by norm_num) e
  have h2 : 3 ^ r ≤ 4 ^ r := Nat.pow_le_pow_left (by norm_num) r
  calc 2 * ((3 ^ 100) ^ e * 3 ^ r) * 16 ^ e = (2 * (3 ^ 100 * 16) ^ e) * 3 ^ r := by
        rw [mul_pow]; ring
    _ ≤ (4 ^ 100) ^ e * 4 ^ r := Nat.mul_le_mul h1 h2

/-- `W(w) ≤ 16^{-e_b}` for a central block at scale `b ≥ 100`. -/
lemma block_wt_le {b K : ℕ} (hb : 100 ≤ b) {w : Word} (hw : w ∈ central b K) :
    wt w ≤ (1 / 16 : ℝ) ^ eB b := by
  have hfc := (central_spec hw).1
  have hA : barrier b w.length ≤ tot w := by rw [← pre_length]; exact hfc.2.2.2.1
  have hnum := two_mul_three_pow_mul_le hb
  have hnum' : 3 ^ b * 16 ^ (b / 100) ≤ 4 ^ b :=
    le_trans (by rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)) hnum
  have key : 3 ^ w.length * 16 ^ eB b ≤ 2 ^ tot w := by
    unfold eB
    rcases le_total w.length b with h | h
    · rw [barrier_of_le h] at hA
      have h1 : 2 * b ≤ tot w + Bc (b - w.length) := by omega
      have h2 := two_pow_Bc_le (b - w.length)
      have h3 : 4 ^ b ≤ 2 ^ tot w * (2 * 3 ^ (b - w.length)) := by
        calc 4 ^ b = 2 ^ (2 * b) := by rw [pow_mul]; norm_num
          _ ≤ 2 ^ (tot w + Bc (b - w.length)) := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 ^ tot w * 2 ^ Bc (b - w.length) := pow_add _ _ _
          _ ≤ 2 ^ tot w * (2 * 3 ^ (b - w.length)) := Nat.mul_le_mul_left _ h2
      have h4 : 3 ^ b = 3 ^ w.length * 3 ^ (b - w.length) := by
        rw [← pow_add]; congr 1; omega
      have h5 : (3 ^ w.length * 16 ^ (b / 100)) * (2 * 3 ^ (b - w.length)) ≤
          2 ^ tot w * (2 * 3 ^ (b - w.length)) := by
        calc (3 ^ w.length * 16 ^ (b / 100)) * (2 * 3 ^ (b - w.length))
            = 2 * 3 ^ b * 16 ^ (b / 100) := by rw [h4]; ring
          _ ≤ 4 ^ b := hnum
          _ ≤ _ := h3
      exact Nat.le_of_mul_le_mul_right h5 (by positivity)
    · rw [barrier_of_ge h] at hA
      have h1 : 2 * b + Bc (w.length - b) ≤ tot w := by omega
      have h2 := three_pow_le_two_pow_Bc (w.length - b)
      have h4 : 3 ^ w.length = 3 ^ b * 3 ^ (w.length - b) := by
        rw [← pow_add]; congr 1; omega
      calc 3 ^ w.length * 16 ^ (b / 100) = (3 ^ b * 16 ^ (b / 100)) * 3 ^ (w.length - b) := by
            rw [h4]; ring
        _ ≤ 4 ^ b * 2 ^ Bc (w.length - b) := Nat.mul_le_mul hnum' h2
        _ = 2 ^ (2 * b + Bc (w.length - b)) := by rw [pow_add, pow_mul]; norm_num
        _ ≤ 2 ^ tot w := Nat.pow_le_pow_right (by norm_num) h1
  have key' : ((3 : ℝ) ^ w.length) * 16 ^ eB b ≤ 2 ^ tot w := by exact_mod_cast key
  have e1 : wt w = 3 ^ w.length / 2 ^ tot w := by
    unfold wt gm; rw [one_div, inv_pow, div_eq_mul_inv]
  rw [e1, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

lemma wt_eq_div (w : Word) : wt w = 3 ^ w.length / 2 ^ tot w := by
  unfold wt gm; rw [one_div, inv_pow, div_eq_mul_inv]

/-! ## (8.6): offset and weight of a history -/

/-- `W R + ϑ = M` for a realisable word. -/
lemma wt_mul_src_add {w : Word} (hw : w.Pos) {M : ℕ} (hM : Odd M) (h : Realizes w M) :
    wt w * (src w M : ℝ) + (thetaW w : ℝ) = M := by
  have e := (realisable_of_realizes hw hM h).1
  have e' : (src w M : ℝ) = ((Phi w M : ℚ) : ℝ) := by rw [← e, Rat.cast_natCast]
  rw [e', wt_eq_div]
  unfold Phi
  push_cast
  field_simp
  ring

lemma wt_flatten_le {b0 : ℕ} (hb0 : 100 ≤ b0) : ∀ (H : List Word) (j : ℕ), BlockTail b0 j H →
    wt H.flatten ≤ (1 / 16 : ℝ) ^ (bseq b0 (j + H.length) - bseq b0 j) := by
  intro H
  induction H with
  | nil => intro j _; simp [wt, gm, tot]
  | cons w H ih =>
    intro j h
    obtain ⟨hw, hH⟩ := blockTail_cons.mp h
    rw [List.flatten_cons, wt_append]
    have h1 := block_wt_le (hb0.trans (le_bseq b0 j)) hw
    have h2 := ih (j + 1) hH
    have hmono := bseq_mono b0 (show j + 1 ≤ j + 1 + H.length by omega)
    have hs : bseq b0 (j + 1) = bseq b0 j + eB (bseq b0 j) := rfl
    have e : bseq b0 (j + (w :: H).length) - bseq b0 j =
        eB (bseq b0 j) + (bseq b0 (j + 1 + H.length) - bseq b0 (j + 1)) := by
      rw [List.length_cons, show j + (H.length + 1) = j + 1 + H.length by omega]
      omega
    rw [e, pow_add]
    exact mul_le_mul h1 h2 (wt_pos _).le (by positivity)

lemma thetaW_flatten_le {b0 : ℕ} (hb0 : 100 ≤ b0) : ∀ (H : List Word) (j : ℕ), BlockTail b0 j H →
    (thetaW H.flatten : ℝ) ≤ 2 ^ (bseq b0 j + 1) := by
  intro H
  induction H with
  | nil => intro j _; rw [List.flatten_nil, thetaW_nil, Rat.cast_zero]; positivity
  | cons w H ih =>
    intro j h
    obtain ⟨hw, hH⟩ := blockTail_cons.mp h
    have hb100 : 100 ≤ bseq b0 j := hb0.trans (le_bseq b0 j)
    have he : 1 ≤ eB (bseq b0 j) := by unfold eB; omega
    rw [List.flatten_cons, thetaW_append]
    push_cast
    have h1 := block_theta_le (by omega) hw
    have h2 := block_wt_le hb100 hw
    have h3 := ih (j + 1) hH
    have hbs : bseq b0 (j + 1) = bseq b0 j + eB (bseq b0 j) := rfl
    rw [hbs] at h3
    rw [← wt_eq_div]
    have h4 : wt w * (thetaW H.flatten : ℝ) ≤
        (1 / 16) ^ eB (bseq b0 j) * 2 ^ (bseq b0 j + eB (bseq b0 j) + 1) :=
      mul_le_mul h2 h3 (by exact_mod_cast thetaW_nonneg _) (by positivity)
    have h5 : (1 / 16 : ℝ) ^ eB (bseq b0 j) * 2 ^ (bseq b0 j + eB (bseq b0 j) + 1) ≤
        2 ^ bseq b0 j := by
      have e : (1 / 16 : ℝ) ^ eB (bseq b0 j) * 2 ^ (bseq b0 j + eB (bseq b0 j) + 1) =
          2 ^ bseq b0 j * (2 * (1 / 8) ^ eB (bseq b0 j)) := by
        rw [pow_add, pow_add, pow_one, show (1 / 8 : ℝ) = 1 / 16 * 2 by norm_num, mul_pow]
        ring
      rw [e]
      have h6 : (1 / 8 : ℝ) ^ eB (bseq b0 j) ≤ 1 / 8 :=
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) he).trans_eq (pow_one _)
      have : (0 : ℝ) < 2 ^ bseq b0 j := by positivity
      nlinarith
    rw [pow_succ]
    linarith

/-- (8.6) with the explicit threshold `b_0 ≥ 100`. -/
lemma history_bounds_of {b0 : ℕ} (hb0 : 100 ≤ b0) {M n : ℕ} (hM : Odd M) {H : List Word}
    (hH : H ∈ hist b0 M n) :
    wt H.flatten * endpt M H + (thetaW H.flatten : ℝ) = M ∧ 0 ≤ (thetaW H.flatten : ℝ) ∧
      (thetaW H.flatten : ℝ) ≤ 2 ^ (b0 + 1) ∧ wt H.flatten ≤ (1 / 16 : ℝ) ^ (bseq b0 n - b0) := by
  obtain ⟨hHb, hR⟩ := mem_hist.mp hH
  obtain ⟨hl, ht⟩ := mem_blocks.mp hHb
  refine ⟨wt_mul_src_add (flatten_pos ht) hM hR, by exact_mod_cast thetaW_nonneg _, ?_, ?_⟩
  · simpa [bseq] using thetaW_flatten_le hb0 H 0 ht
  · have := wt_flatten_le hb0 H 0 ht
    simpa [hl, bseq] using this

/-- **(8.6, `eq:C3`)**: a history of `n` blocks from an odd seed `M`, with weight `W`, endpoint
`R` and offset `ϑ`, satisfies `W R + ϑ = M`, `0 ≤ ϑ ≤ 2^{b_0+1}` and `W ≤ 16^{b_0-b_n}`. -/
theorem history_bounds : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∀ M n : ℕ, Odd M → ∀ H ∈ hist b0 M n,
    wt H.flatten * endpt M H + (thetaW H.flatten : ℝ) = M ∧ 0 ≤ (thetaW H.flatten : ℝ) ∧
      (thetaW H.flatten : ℝ) ≤ 2 ^ (b0 + 1) ∧ wt H.flatten ≤ (1 / 16 : ℝ) ^ (bseq b0 n - b0) :=
  ⟨100, fun _ hb0 _ _ hM _ hH => history_bounds_of hb0 hM hH⟩

/-- **Endpoints stay large** (the sentence of §8.2 after (8.5)): for a seed `M ≥ 16^{b_0}`, every
generation-`n` endpoint is `≥ 16^{b_n}/2`. The paper's `≥ 16^{b_j}` comes from the lower bound of
(8.5) by induction; this form follows from (8.6) and suffices for `phi_bounds`. -/
lemma endpt_ge {b0 : ℕ} (hb0 : 100 ≤ b0) {M n : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    {H : List Word} (hH : H ∈ hist b0 M n) : (16 : ℝ) ^ bseq b0 n / 2 ≤ endpt M H := by
  obtain ⟨e, -, h1, hw⟩ := history_bounds_of hb0 hM hH
  obtain ⟨k, hk⟩ : ∃ k, bseq b0 n = b0 + k := ⟨bseq b0 n - b0, by have := le_bseq b0 n; omega⟩
  rw [hk, Nat.add_sub_cancel_left] at hw
  have hW := wt_pos H.flatten
  have hM' : (16 : ℝ) ^ b0 ≤ M := by exact_mod_cast hM16
  have h2 : (2 : ℝ) ^ (b0 + 2) ≤ 16 ^ b0 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2' : (2 : ℝ) ^ (b0 + 2) = 2 * 2 ^ (b0 + 1) := by rw [pow_succ]; ring
  have hWR : (16 : ℝ) ^ b0 / 2 ≤ wt H.flatten * endpt M H := by linarith
  have h16 : (0 : ℝ) ≤ 16 ^ k := by positivity
  have hk' : (16 : ℝ) ^ k * wt H.flatten ≤ 1 := by
    have : (16 : ℝ) ^ k * (1 / 16) ^ k = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  have hR0 : (0 : ℝ) ≤ endpt M H := Nat.cast_nonneg _
  rw [hk, pow_add]
  nlinarith [mul_le_mul_of_nonneg_left hWR h16, mul_le_mul_of_nonneg_right hk' hR0]

/-! ## (8.5): one block moves the scale by `(4/3)^b` -/

/-- `4^b 3^s ≤ 2·3^b 2^{A}` and `2^{A} 3^b ≤ 2^{K+1} 4^b 3^s` for a central block of depth `s` and
total `A` (from `3^t ≤ 2^{B(t)} ≤ 2·3^t`). -/
lemma block_pow_bounds {b K : ℕ} {w : Word} (hw : w ∈ central b K) :
    4 ^ b * 3 ^ w.length ≤ 2 * 3 ^ b * 2 ^ tot w ∧
      2 ^ tot w * 3 ^ b ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length := by
  have hfc := (central_spec hw).1
  have hA1 : barrier b w.length ≤ tot w := by rw [← pre_length]; exact hfc.2.2.2.1
  have hA2 : (tot w : ℤ) ≤ barrier b w.length + K := by rw [← pre_length]; exact hfc.2.2.2.2
  have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := by rw [pow_mul]; norm_num
  rcases le_total w.length b with h | h
  · rw [barrier_of_le h] at hA1 hA2
    have hb3 : 3 ^ b = 3 ^ w.length * 3 ^ (b - w.length) := by rw [← pow_add]; congr 1; omega
    have hB1 := two_pow_Bc_le (b - w.length)
    have hB2 := three_pow_le_two_pow_Bc (b - w.length)
    constructor
    · have e1 : 2 * b ≤ tot w + Bc (b - w.length) := by omega
      have : 4 ^ b ≤ 2 ^ tot w * (2 * 3 ^ (b - w.length)) := by
        calc 4 ^ b = 2 ^ (2 * b) := h4
          _ ≤ 2 ^ (tot w + Bc (b - w.length)) := Nat.pow_le_pow_right (by norm_num) e1
          _ = 2 ^ tot w * 2 ^ Bc (b - w.length) := pow_add _ _ _
          _ ≤ 2 ^ tot w * (2 * 3 ^ (b - w.length)) := Nat.mul_le_mul_left _ hB1
      calc 4 ^ b * 3 ^ w.length ≤ 2 ^ tot w * (2 * 3 ^ (b - w.length)) * 3 ^ w.length :=
            Nat.mul_le_mul_right _ this
        _ = 2 * 3 ^ b * 2 ^ tot w := by rw [hb3]; ring
    · have e2 : tot w + Bc (b - w.length) ≤ 2 * b + K := by omega
      have : 2 ^ tot w * 3 ^ (b - w.length) ≤ 2 ^ K * 4 ^ b := by
        calc 2 ^ tot w * 3 ^ (b - w.length) ≤ 2 ^ tot w * 2 ^ Bc (b - w.length) :=
              Nat.mul_le_mul_left _ hB2
          _ = 2 ^ (tot w + Bc (b - w.length)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ (2 * b + K) := Nat.pow_le_pow_right (by norm_num) e2
          _ = 2 ^ K * 4 ^ b := by rw [pow_add, h4]; ring
      calc 2 ^ tot w * 3 ^ b = (2 ^ tot w * 3 ^ (b - w.length)) * 3 ^ w.length := by rw [hb3]; ring
        _ ≤ (2 ^ K * 4 ^ b) * 3 ^ w.length := Nat.mul_le_mul_right _ this
        _ ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length := by rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ K * 4 ^ b * 3 ^ w.length)]
  · rw [barrier_of_ge h] at hA1 hA2
    have hd3 : 3 ^ w.length = 3 ^ b * 3 ^ (w.length - b) := by rw [← pow_add]; congr 1; omega
    have hB1 := two_pow_Bc_le (w.length - b)
    have hB2 := three_pow_le_two_pow_Bc (w.length - b)
    constructor
    · have e1 : 2 * b + Bc (w.length - b) ≤ tot w := by omega
      have : 4 ^ b * 3 ^ (w.length - b) ≤ 2 ^ tot w := by
        calc 4 ^ b * 3 ^ (w.length - b) ≤ 2 ^ (2 * b) * 2 ^ Bc (w.length - b) := by
              rw [← h4]; exact Nat.mul_le_mul_left _ hB2
          _ = 2 ^ (2 * b + Bc (w.length - b)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ tot w := Nat.pow_le_pow_right (by norm_num) e1
      calc 4 ^ b * 3 ^ w.length = (4 ^ b * 3 ^ (w.length - b)) * 3 ^ b := by rw [hd3]; ring
        _ ≤ 2 ^ tot w * 3 ^ b := Nat.mul_le_mul_right _ this
        _ ≤ 2 * 3 ^ b * 2 ^ tot w := by nlinarith [Nat.zero_le (2 ^ tot w * 3 ^ b)]
    · have e2 : tot w ≤ 2 * b + Bc (w.length - b) + K := by omega
      calc 2 ^ tot w * 3 ^ b ≤ 2 ^ (2 * b + Bc (w.length - b) + K) * 3 ^ b :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) e2)
        _ = 2 ^ K * 4 ^ b * 2 ^ Bc (w.length - b) * 3 ^ b := by rw [pow_add, pow_add, h4]; ring
        _ ≤ 2 ^ K * 4 ^ b * (2 * 3 ^ (w.length - b)) * 3 ^ b :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hB1)
        _ = 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length := by rw [hd3, pow_succ]; ring

/-- **(8.5, `eq:C2`)**: a central block `w` at scale `b` applied to a target `R ≥ 2^{b+1}` gives
`(1/4)(4/3)^b R ≤ Φ_w(R) ≤ 2^{K+1}(4/3)^b R` (the paper's `R - ϑ_w ≥ R/2` is where `R ≥ 2^{b+1}`
is used; the upper bound needs only `R ≥ 0`). -/
theorem phi_bounds {b K : ℕ} (hb : 32 ≤ b) {w : Word} (hw : w ∈ central b K) {R : ℚ}
    (hR : 2 ^ (b + 1) ≤ R) :
    1 / 4 * (4 / 3) ^ b * R ≤ Phi w R ∧ Phi w R ≤ 2 ^ (K + 1) * (4 / 3) ^ b * R := by
  obtain ⟨hl, hu⟩ := block_pow_bounds hw
  have hl' : (4 : ℚ) ^ b * 3 ^ w.length ≤ 2 * 3 ^ b * 2 ^ tot w := by exact_mod_cast hl
  have hu' : (2 : ℚ) ^ tot w * 3 ^ b ≤ 2 ^ (K + 1) * 4 ^ b * 3 ^ w.length := by exact_mod_cast hu
  have hth : thetaW w ≤ 2 ^ b := by
    have := block_theta_le hb hw
    exact_mod_cast this
  have hth0 := thetaW_nonneg w
  have h2b : (2 : ℚ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hd : (0 : ℚ) < 3 ^ w.length := by positivity
  have h3b : (0 : ℚ) < 3 ^ b := by positivity
  have hA : (0 : ℚ) < 2 ^ tot w := by positivity
  unfold Phi
  rw [div_pow]
  constructor
  · rw [le_div_iff₀ hd]
    have e : 1 / 4 * (4 ^ b / 3 ^ b) * R * 3 ^ w.length = (4 ^ b * 3 ^ w.length) * R / (4 * 3 ^ b) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h1 : R ≤ 2 * (R - thetaW w) := by linarith
    calc 4 ^ b * 3 ^ w.length * R ≤ 2 * 3 ^ b * 2 ^ tot w * R := mul_le_mul_of_nonneg_right hl' hR0
      _ ≤ 2 * 3 ^ b * 2 ^ tot w * (2 * (R - thetaW w)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ tot w * (R - thetaW w) * (4 * 3 ^ b) := by ring
  · rw [div_le_iff₀ hd]
    have h1 : R - thetaW w ≤ R := by linarith
    have e : 2 ^ (K + 1) * (4 ^ b / 3 ^ b) * R * 3 ^ w.length =
        (2 ^ (K + 1) * 4 ^ b * 3 ^ w.length) * R / 3 ^ b := by field_simp
    rw [e, le_div_iff₀ h3b]
    calc 2 ^ tot w * (R - thetaW w) * 3 ^ b ≤ 2 ^ tot w * R * 3 ^ b := by
          have := mul_le_mul_of_nonneg_left h1 hA.le
          nlinarith
      _ = (2 ^ tot w * 3 ^ b) * R := by ring
      _ ≤ (2 ^ (K + 1) * 4 ^ b * 3 ^ w.length) * R := mul_le_mul_of_nonneg_right hu' hR0

/-! ## Proposition 8.5: endpoints at a fixed depth and valuation -/

/-- A source and a depth determine the word (Lemma 2.1 [`lem:inverse`], `source_exists`). -/
lemma word_eq_of_src {M : ℕ} (hMo : Odd M) {w w' : Word} (hw : w.Pos) (hw' : w'.Pos)
    (h : Realizes w M) (h' : Realizes w' M) (hlen : w.length = w'.length)
    (hx : src w M = src w' M) : w = w' := by
  obtain ⟨-, -, hv, -⟩ := realisable_of_realizes hw hMo h
  obtain ⟨-, -, hv', -⟩ := realisable_of_realizes hw' hMo h'
  rw [hx] at hv
  apply List.reverse_injective
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have hi : i < w.length := by simpa using h1
  have e := (hv i hi).symm.trans (hv' i (by omega))
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e

/-- Two histories with the same depth and the same endpoint coincide: the endpoint and the depth
determine the flattened word, and the first-crossing cuts are determined by the word. -/
lemma hist_inj {b0 M n : ℕ} (hMo : Odd M) {H H' : List Word} (hH : H ∈ hist b0 M n)
    (hH' : H' ∈ hist b0 M n) (hlen : H.flatten.length = H'.flatten.length)
    (he : endpt M H = endpt M H') : H = H' := by
  obtain ⟨hb, hr⟩ := mem_hist.mp hH
  obtain ⟨hb', hr'⟩ := mem_hist.mp hH'
  obtain ⟨hl, ht⟩ := mem_blocks.mp hb
  obtain ⟨hl', ht'⟩ := mem_blocks.mp hb'
  have hf := word_eq_of_src hMo (flatten_pos ht) (flatten_pos ht') hr hr' hlen he
  exact flatten_inj (V := fun j => central (bseq b0 j) (Kseq j)) (fun j => central_prefixFree _ _)
    H H' (hl.trans hl'.symm) (fun j h => by simpa using ht j h) (fun j h => by simpa using ht' j h)
    hf

/-- A residue class mod `Q` meets `[lo, hi]` in at most `⌊(hi - lo)/Q⌋ + 1` points. -/
lemma card_filter_modEq_le (lo hi Q c : ℕ) :
    ((Icc lo hi).filter (fun N => N ≡ c [MOD Q])).card ≤ (hi - lo) / Q + 1 := by
  rw [← Finset.card_range ((hi - lo) / Q + 1)]
  apply Finset.card_le_card_of_injOn (fun N => (N - lo) / Q)
  · intro N hN
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hN
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · intro N hN N' hN' h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hN hN'
    have hm : N - lo ≡ N' - lo [MOD Q] := by
      apply Nat.ModEq.add_right_cancel' lo
      rw [Nat.sub_add_cancel hN.1.1, Nat.sub_add_cancel hN'.1.1]
      exact hN.2.trans hN'.2.symm
    have h1 := Nat.div_add_mod (N - lo) Q
    have h2 := Nat.div_add_mod (N' - lo) Q
    simp only at h
    unfold Nat.ModEq at hm
    rw [h, hm] at h1
    omega

/-- **The fibre bound.** Histories with the same depth `D` and valuation `A` have the same weight
`W = 3^D 2^{-A}` and distinct endpoints in an interval of length `2^{b_0+1}/W` (by (8.6)); so each
residue class mod `3^q` carries at most `2^{b_0+1}/(W 3^q) + 1` of them. -/
lemma fiber_bound {b0 : ℕ} (hb0 : 100 ≤ b0) {M n q : ℕ} (hM : Odd M) (y : ZMod (3 ^ q))
    (D A : ℕ) {S : Finset (List Word)}
    (hS : ∀ H ∈ S, H ∈ hist b0 M n ∧ H.flatten.length = D ∧ tot H.flatten = A)
    (hy : ∀ H ∈ S, ((endpt M H : ℕ) : ZMod (3 ^ q)) = y) :
    (3 : ℝ) ^ q * ((S.card : ℝ) * (3 ^ D / 2 ^ A)) ≤ 2 ^ (b0 + 1) + 3 ^ D / 2 ^ A * 3 ^ q := by
  have hWpos : (0 : ℝ) < 3 ^ D / 2 ^ A := by positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨H0, hH0⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero]; positivity
  have hwt : ∀ H ∈ S, wt H.flatten = 3 ^ D / 2 ^ A := fun H hH => by
    rw [wt_eq_div, (hS H hH).2.1, (hS H hH).2.2]
  have hR : ∀ H ∈ S, ((M : ℝ) - 2 ^ (b0 + 1)) / (3 ^ D / 2 ^ A) ≤ endpt M H ∧
      (endpt M H : ℝ) ≤ M / (3 ^ D / 2 ^ A) := by
    intro H hH
    obtain ⟨e, h0, h1, -⟩ := history_bounds_of hb0 hM (hS H hH).1
    rw [hwt H hH] at e
    constructor
    · rw [div_le_iff₀ hWpos]; linarith
    · rw [le_div_iff₀ hWpos]; linarith
  have hmem : ∀ H ∈ S, endpt M H ∈ (Icc ⌈((M : ℝ) - 2 ^ (b0 + 1)) / (3 ^ D / 2 ^ A)⌉₊
      ⌊(M : ℝ) / (3 ^ D / 2 ^ A)⌋₊).filter (fun N => N ≡ y.val [MOD 3 ^ q]) := by
    intro H hH
    obtain ⟨h1, h2⟩ := hR H hH
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩, ?_⟩
    have := hy H hH
    rw [← ZMod.natCast_zmod_val y, ZMod.natCast_eq_natCast_iff] at this
    exact this
  set lo := ⌈((M : ℝ) - 2 ^ (b0 + 1)) / (3 ^ D / 2 ^ A)⌉₊ with hlo
  set hi := ⌊(M : ℝ) / (3 ^ D / 2 ^ A)⌋₊ with hhi
  have hinj : Set.InjOn (endpt M) S := by
    intro H hH H' hH' he
    exact hist_inj hM (hS H hH).1 (hS H' hH').1 ((hS H hH).2.1.trans (hS H' hH').2.1.symm) he
  have hcard : S.card ≤ (hi - lo) / 3 ^ q + 1 :=
    (Finset.card_le_card_of_injOn (endpt M) (fun H hH => hmem H hH) hinj).trans
      (card_filter_modEq_le lo hi (3 ^ q) _)
  have hlohi : lo ≤ hi := by
    have := hmem H0 hH0
    rw [Finset.mem_filter, Finset.mem_Icc] at this
    obtain ⟨⟨h1, h2⟩, -⟩ := this
    omega
  have hlen : (3 ^ D / 2 ^ A : ℝ) * ((hi - lo : ℕ) : ℝ) ≤ 2 ^ (b0 + 1) := by
    rw [Nat.cast_sub hlohi]
    have h1 : (hi : ℝ) ≤ M / (3 ^ D / 2 ^ A) := Nat.floor_le (by positivity)
    have h2 : ((M : ℝ) - 2 ^ (b0 + 1)) / (3 ^ D / 2 ^ A) ≤ lo := Nat.le_ceil _
    have h3 : (M : ℝ) / (3 ^ D / 2 ^ A) - ((M : ℝ) - 2 ^ (b0 + 1)) / (3 ^ D / 2 ^ A) =
        2 ^ (b0 + 1) / (3 ^ D / 2 ^ A) := by ring
    have h4 : (hi : ℝ) - lo ≤ 2 ^ (b0 + 1) / (3 ^ D / 2 ^ A) := by linarith
    calc (3 ^ D / 2 ^ A : ℝ) * ((hi : ℝ) - lo)
        ≤ (3 ^ D / 2 ^ A) * (2 ^ (b0 + 1) / (3 ^ D / 2 ^ A)) :=
          mul_le_mul_of_nonneg_left h4 hWpos.le
      _ = 2 ^ (b0 + 1) := by field_simp
  have h3q : (0 : ℝ) < 3 ^ q := by positivity
  have hcardR : (S.card : ℝ) ≤ ((hi - lo : ℕ) : ℝ) / 3 ^ q + 1 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at h
    have h2 : (((hi - lo) / 3 ^ q : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) / ((3 ^ q : ℕ) : ℝ) :=
      Nat.cast_div_le
    push_cast at h2
    linarith
  calc (3 : ℝ) ^ q * ((S.card : ℝ) * (3 ^ D / 2 ^ A))
      ≤ 3 ^ q * ((((hi - lo : ℕ) : ℝ) / 3 ^ q + 1) * (3 ^ D / 2 ^ A)) := by gcongr
    _ = (3 ^ D / 2 ^ A) * ((hi - lo : ℕ) : ℝ) + 3 ^ D / 2 ^ A * 3 ^ q := by field_simp
    _ ≤ 2 ^ (b0 + 1) + 3 ^ D / 2 ^ A * 3 ^ q := by linarith

/-! ## Proposition 8.5: the number of pairs `(D, A)` -/

/-- `∑_{i<k} b_{j+i}`. -/
def Bsum (b0 j k : ℕ) : ℕ := ∑ i ∈ range k, bseq b0 (j + i)

/-- `∑_{i<k} ⌈b_{j+i}^{3/5}⌉`. -/
def Msum (b0 j k : ℕ) : ℕ := ∑ i ∈ range k, mB (bseq b0 (j + i))

/-- `∑_{i<k} K_{j+i}`. -/
def Ksum (j k : ℕ) : ℕ := ∑ i ∈ range k, Kseq (j + i)

lemma sum_range_succ_shift (f : ℕ → ℕ) (j k : ℕ) :
    ∑ i ∈ range (k + 1), f (j + i) = f j + ∑ i ∈ range k, f (j + 1 + i) := by
  rw [Finset.sum_range_succ', add_comm, Nat.add_zero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [show j + (i + 1) = j + 1 + i by omega]

lemma Bsum_succ (b0 j k : ℕ) : Bsum b0 j (k + 1) = bseq b0 j + Bsum b0 (j + 1) k :=
  sum_range_succ_shift (bseq b0) j k

lemma Msum_succ (b0 j k : ℕ) : Msum b0 j (k + 1) = mB (bseq b0 j) + Msum b0 (j + 1) k :=
  sum_range_succ_shift (fun i => mB (bseq b0 i)) j k

lemma Ksum_succ (j k : ℕ) : Ksum j (k + 1) = Kseq j + Ksum (j + 1) k :=
  sum_range_succ_shift Kseq j k

/-- One block: `|s - b| ≤ ⌈b^{3/5}⌉` and `-1 ≤ A(w) - 2b - θ(s - b) ≤ K + 1`, from
`θ t ≤ B(t) < θ t + 1`. -/
lemma block_DA {b K : ℕ} {w : Word} (hw : w ∈ central b K) :
    (b : ℤ) ≤ w.length + mB b ∧ (w.length : ℤ) ≤ b + mB b ∧
      -1 ≤ (tot w : ℝ) - 2 * b - θ * ((w.length : ℝ) - b) ∧
      (tot w : ℝ) - 2 * b - θ * ((w.length : ℝ) - b) ≤ K + 1 := by
  obtain ⟨hfc, hl1, hl2⟩ := central_spec hw
  have hA1 : barrier b w.length ≤ tot w := by rw [← pre_length]; exact hfc.2.2.2.1
  have hA2 : (tot w : ℤ) ≤ barrier b w.length + K := by rw [← pre_length]; exact hfc.2.2.2.2
  refine ⟨by omega, by omega, ?_⟩
  have hA1' : ((barrier b w.length : ℤ) : ℝ) ≤ (tot w : ℝ) := by exact_mod_cast hA1
  have hA2' : (tot w : ℝ) ≤ ((barrier b w.length : ℤ) : ℝ) + K := by exact_mod_cast hA2
  rcases le_total w.length b with h | h
  · rw [barrier_of_le h] at hA1' hA2'
    push_cast at hA1' hA2'
    have t1 := theta_mul_le_Bc (b - w.length)
    have t2 := Bc_lt_theta_mul_add_one (b - w.length)
    rw [Nat.cast_sub h] at t1 t2
    constructor <;> linarith
  · rw [barrier_of_ge h] at hA1' hA2'
    push_cast at hA1' hA2'
    have t1 := theta_mul_le_Bc (w.length - b)
    have t2 := Bc_lt_theta_mul_add_one (w.length - b)
    rw [Nat.cast_sub h] at t1 t2
    constructor <;> linarith

/-- A run of blocks: `|D - ∑ b| ≤ ∑ ⌈b^{3/5}⌉` and `-k ≤ A - 2∑ b - θ(D - ∑ b) ≤ ∑ K + k`. -/
lemma tail_DA (b0 : ℕ) : ∀ (H : List Word) (j : ℕ), BlockTail b0 j H →
    (Bsum b0 j H.length : ℤ) ≤ H.flatten.length + Msum b0 j H.length ∧
    (H.flatten.length : ℤ) ≤ Bsum b0 j H.length + Msum b0 j H.length ∧
    -(H.length : ℝ) ≤ (tot H.flatten : ℝ) - 2 * Bsum b0 j H.length -
      θ * ((H.flatten.length : ℝ) - Bsum b0 j H.length) ∧
    (tot H.flatten : ℝ) - 2 * Bsum b0 j H.length -
      θ * ((H.flatten.length : ℝ) - Bsum b0 j H.length) ≤ Ksum j H.length + H.length := by
  intro H
  induction H with
  | nil => intro j _; simp [Bsum, Msum, Ksum, tot]
  | cons w H ih =>
    intro j h
    obtain ⟨hw, hH⟩ := blockTail_cons.mp h
    obtain ⟨a1, a2, a3, a4⟩ := block_DA hw
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) hH
    rw [List.length_cons, Bsum_succ, Msum_succ, Ksum_succ, List.flatten_cons, List.length_append,
      tot_append]
    push_cast at a1 a2 a3 a4 b1 b2 b3 b4 ⊢
    refine ⟨by omega, by omega, by linarith, by linarith⟩

/-- The shift that sends the valuations at depth `D` into `[0, K_* + 2n]`. -/
def keyShift (b0 n D : ℕ) : ℕ := ⌈2 * (Bsum b0 0 n : ℝ) + θ * ((D : ℝ) - Bsum b0 0 n) - n⌉₊

/-- At most `(2M_* + 1)(K_* + 4n + 1)` pairs `(D, A)` occur. -/
lemma card_keys_le (b0 M n : ℕ) :
    ((hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten))).card ≤
      (2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) := by
  have hM : Msum b0 0 n = Mstar b0 n := by simp [Msum, Mstar]
  have hK : Ksum 0 n = Kstar n := by simp [Ksum, Kstar]
  have hfacts : ∀ p : ℕ × ℕ, p ∈ (hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten)) →
      (Bsum b0 0 n : ℤ) ≤ p.1 + Mstar b0 n ∧ (p.1 : ℤ) ≤ Bsum b0 0 n + Mstar b0 n ∧
        keyShift b0 n p.1 ≤ p.2 ∧ p.2 ≤ keyShift b0 n p.1 + (Kstar n + 2 * n) := by
    intro p hp
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hp
    dsimp only
    obtain ⟨hl, ht⟩ := mem_blocks.mp (mem_hist.mp hH).1
    obtain ⟨d1, d2, d3, d4⟩ := tail_DA b0 H 0 ht
    rw [hl, hM] at d1 d2
    rw [hl, hK] at d4
    rw [hl] at d3
    refine ⟨d1, d2, Nat.ceil_le.mpr (by linarith), ?_⟩
    have hc := Nat.le_ceil (2 * (Bsum b0 0 n : ℝ) + θ * ((H.flatten.length : ℝ) - Bsum b0 0 n) - n)
    have : (tot H.flatten : ℝ) ≤ keyShift b0 n H.flatten.length + (Kstar n + 2 * n) := by
      unfold keyShift; linarith
    exact_mod_cast this
  calc ((hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten))).card
      ≤ ((Icc (Bsum b0 0 n - Mstar b0 n) (Bsum b0 0 n + Mstar b0 n)) ×ˢ
          range (Kstar n + 2 * n + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1, p.2 - keyShift b0 n p.1))
        · intro p hp
          obtain ⟨f1, f2, f3, f4⟩ := hfacts p hp
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
          refine ⟨⟨by omega, by omega⟩, by omega⟩
        · intro p hp p' hp' h
          obtain ⟨-, -, f3, -⟩ := hfacts p hp
          obtain ⟨-, -, f3', -⟩ := hfacts p' hp'
          simp only [Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          rw [h1] at f3 h2
          exact Prod.ext h1 (by omega)
    _ = (Bsum b0 0 n + Mstar b0 n + 1 - (Bsum b0 0 n - Mstar b0 n)) * (Kstar n + 2 * n + 1) := by
        rw [Finset.card_product, Nat.card_Icc, Finset.card_range]
    _ ≤ (2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) := Nat.mul_le_mul (by omega) (by omega)

/-! ## Proposition 8.5 -/

lemma histo_nonneg (b0 M n q : ℕ) (y : ZMod (3 ^ q)) : 0 ≤ histo b0 M n q y :=
  Finset.sum_nonneg fun H _ => by split_ifs; exacts [(wt_pos _).le, le_rfl]

/-- (8.7) with the explicit threshold `b_0 ≥ 100`, for every odd seed. -/
theorem histogram_bound_of {b0 : ℕ} (hb0 : 100 ≤ b0) {M n q : ℕ} (hM : Odd M)
    (hq : q ≤ 2 * bseq b0 n) (y : ZMod (3 ^ q)) :
    3 ^ q * histo b0 M n q y ≤ (2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
      (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n) := by
  classical
  have hsplit : histo b0 M n q y =
      ∑ p ∈ (hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten)),
        ∑ H ∈ (hist b0 M n).filter (fun H => (H.flatten.length, tot H.flatten) = p),
          (if ((endpt M H : ℕ) : ZMod (3 ^ q)) = y then wt H.flatten else 0) := by
    unfold histo
    exact (Finset.sum_fiberwise_of_maps_to (fun H hH => Finset.mem_image_of_mem _ hH) _).symm
  rw [hsplit, Finset.mul_sum]
  have hterm : ∀ p ∈ (hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten)),
      (3 : ℝ) ^ q * ∑ H ∈ (hist b0 M n).filter (fun H => (H.flatten.length, tot H.flatten) = p),
        (if ((endpt M H : ℕ) : ZMod (3 ^ q)) = y then wt H.flatten else 0) ≤
      2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n := by
    intro p hp
    obtain ⟨H0, hH0, rfl⟩ := Finset.mem_image.mp hp
    rw [← Finset.sum_filter]
    have hS : ∀ H ∈ ((hist b0 M n).filter (fun H =>
        (H.flatten.length, tot H.flatten) = (H0.flatten.length, tot H0.flatten))).filter
          (fun H => ((endpt M H : ℕ) : ZMod (3 ^ q)) = y),
        H ∈ hist b0 M n ∧ H.flatten.length = H0.flatten.length ∧ tot H.flatten = tot H0.flatten := by
      intro H hH
      simp only [Finset.mem_filter, Prod.mk.injEq] at hH
      exact ⟨hH.1.1, hH.1.2.1, hH.1.2.2⟩
    have hwtS : ∑ H ∈ ((hist b0 M n).filter (fun H =>
        (H.flatten.length, tot H.flatten) = (H0.flatten.length, tot H0.flatten))).filter
          (fun H => ((endpt M H : ℕ) : ZMod (3 ^ q)) = y), wt H.flatten =
        (((((hist b0 M n).filter (fun H =>
          (H.flatten.length, tot H.flatten) = (H0.flatten.length, tot H0.flatten))).filter
            (fun H => ((endpt M H : ℕ) : ZMod (3 ^ q)) = y)).card : ℕ) : ℝ) *
          (3 ^ H0.flatten.length / 2 ^ tot H0.flatten) := by
      rw [Finset.sum_congr rfl (fun H hH => by rw [wt_eq_div, (hS H hH).2.1, (hS H hH).2.2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hwtS]
    refine (fiber_bound hb0 hM y _ _ hS (fun H hH => (Finset.mem_filter.mp hH).2)).trans ?_
    suffices hX : 3 ^ H0.flatten.length / 2 ^ tot H0.flatten * (3 : ℝ) ^ q ≤
        16 ^ b0 * (9 / 16) ^ bseq b0 n by linarith
    have h3q : (3 : ℝ) ^ q ≤ 9 ^ bseq b0 n := by
      calc (3 : ℝ) ^ q ≤ 3 ^ (2 * bseq b0 n) := pow_le_pow_right₀ (by norm_num) hq
        _ = 9 ^ bseq b0 n := by rw [pow_mul]; norm_num
    have hwb := (history_bounds_of hb0 hM hH0).2.2.2
    rw [wt_eq_div] at hwb
    obtain ⟨k, hk⟩ : ∃ k, bseq b0 n = b0 + k := ⟨bseq b0 n - b0, by have := le_bseq b0 n; omega⟩
    calc 3 ^ H0.flatten.length / 2 ^ tot H0.flatten * (3 : ℝ) ^ q
        ≤ (1 / 16) ^ (bseq b0 n - b0) * 9 ^ bseq b0 n :=
          mul_le_mul hwb h3q (by positivity) (by positivity)
      _ = 16 ^ b0 * (9 / 16) ^ bseq b0 n := by
          rw [hk, Nat.add_sub_cancel_left]; simp only [div_pow, one_pow]; field_simp; ring
  calc ∑ p ∈ (hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten)),
        (3 : ℝ) ^ q * ∑ H ∈ (hist b0 M n).filter (fun H => (H.flatten.length, tot H.flatten) = p),
          (if ((endpt M H : ℕ) : ZMod (3 ^ q)) = y then wt H.flatten else 0)
      ≤ ∑ p ∈ (hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten)),
          (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n) := Finset.sum_le_sum hterm
    _ = (((hist b0 M n).image (fun H => (H.flatten.length, tot H.flatten))).card : ℝ) *
          (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) : ℕ) : ℝ) *
          (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n) := by
        gcongr; exact_mod_cast card_keys_le b0 M n
    _ = _ := by push_cast; ring

/-- **Proposition 8.5 [`prop:C4`]**, (8.7, `eq:C4`): the seed-independent histogram bound
`3^q 𝓗_{n,q}(y) ≤ (2M_* + 1)(K_* + 4n + 1)[2^{b_0+1} + 16^{b_0}(9/16)^{b_n}]` for `q ≤ 2b_n`. -/
theorem histogram_bound : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∀ M n q : ℕ, Odd M → 16 ^ b0 ≤ M →
    q ≤ 2 * bseq b0 n → ∀ y : ZMod (3 ^ q),
      3 ^ q * histo b0 M n q y ≤ (2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
        (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n) :=
  ⟨100, fun _ hb0 _ _ _ hM _ hq y => histogram_bound_of hb0 hM hq y⟩

lemma Kstar_le (n : ℕ) : Kstar n ≤ n * n := by
  unfold Kstar
  calc ∑ j ∈ range n, Kseq j ≤ ∑ _j ∈ range n, n :=
        Finset.sum_le_sum fun j hj => by unfold Kseq; rw [Finset.mem_range] at hj; omega
    _ = n * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma one_le_Gc : 1 ≤ Gc := by unfold Gc; norm_num

/-- `b_j^{3/5} ≤ b_0 G^j`, since `(101/100)^{3/5} < G`. -/
lemma rpow_bseq_le {b0 : ℕ} (hb0 : 1 ≤ b0) (j : ℕ) :
    (bseq b0 j : ℝ) ^ (3 / 5 : ℝ) ≤ b0 * Gc ^ j := by
  have h0 : (0 : ℝ) ≤ (bseq b0 j : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have hb : (1 : ℝ) ≤ b0 := by exact_mod_cast hb0
  have hG := one_le_Gc
  have h1 : ((bseq b0 j : ℝ) ^ (3 / 5 : ℝ)) ^ 5 ≤ ((b0 : ℝ) * Gc ^ j) ^ 5 := by
    rw [rpow_three_fifths_pow_five]
    have hu := bseq_upper b0 j
    have hG5 : (101 / 100 : ℝ) ^ 3 ≤ Gc ^ 5 := by unfold Gc; norm_num
    calc (bseq b0 j : ℝ) ^ 3 ≤ ((b0 : ℝ) * (101 / 100) ^ j) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hu 3
      _ = (b0 : ℝ) ^ 3 * ((101 / 100) ^ 3) ^ j := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 3]
      _ ≤ (b0 : ℝ) ^ 5 * (Gc ^ 5) ^ j :=
          mul_le_mul (pow_le_pow_right₀ hb (by norm_num)) (pow_le_pow_left₀ (by norm_num) hG5 j)
            (by positivity) (by positivity)
      _ = ((b0 : ℝ) * Gc ^ j) ^ 5 := by ring
  exact (pow_le_pow_iff_left₀ h0 (by positivity) (by norm_num)).mp h1

lemma Mstar_le {b0 : ℕ} (hb0 : 1 ≤ b0) (n : ℕ) : (Mstar b0 n : ℝ) ≤ n + b0 * n * Gc ^ n := by
  unfold Mstar
  push_cast
  have hG := one_le_Gc
  calc ∑ j ∈ range n, (mB (bseq b0 j) : ℝ) ≤ ∑ _j ∈ range n, (1 + b0 * Gc ^ n) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        have h1 : (mB (bseq b0 j) : ℝ) < (bseq b0 j : ℝ) ^ (3 / 5 : ℝ) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        have h2 := rpow_bseq_le hb0 j
        have h3 : Gc ^ j ≤ Gc ^ n := pow_le_pow_right₀ hG hj.le
        have hb : (0 : ℝ) ≤ b0 := Nat.cast_nonneg _
        nlinarith
    _ = n + b0 * n * Gc ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Proposition 8.5 [`prop:C4`]**, (8.8, `eq:C5`): pairing the histogram with a test function,
`|∑_y 𝓗_{n,q}(y) f(y)| ≤ C_{b_0} (n+1)^3 G^n ‖f‖_{L¹(G_q)}` for `q ≤ 2b_n`, `G = 2013/2000`. -/
theorem histogram_pairing : ∃ b₁ : ℕ, ∀ b0 ≥ b₁, ∃ C : ℝ, ∀ M n q : ℕ, Odd M → 16 ^ b0 ≤ M →
    q ≤ 2 * bseq b0 n → ∀ f : ZMod (3 ^ q) → ℝ,
      |∑ y, histo b0 M n q y * f y| ≤ C * (n + 1) ^ 3 * Gc ^ n * normL1 q f := by
  refine ⟨100, fun b0 hb0 => ⟨5 * (3 + 2 * b0) * (2 ^ (b0 + 1) + 16 ^ b0),
    fun M n q hM _ hq f => ?_⟩⟩
  have hb1 : 1 ≤ b0 := by omega
  have h3q : (0 : ℝ) < 3 ^ q := by positivity
  have hpt : ∀ y, histo b0 M n q y ≤ ((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
      (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n)) / 3 ^ q := fun y => by
    rw [le_div_iff₀ h3q, mul_comm]; exact histogram_bound_of hb0 hM hq y
  have h1 : |∑ y, histo b0 M n q y * f y| ≤ ((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
      (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n)) * normL1 q f := by
    calc |∑ y, histo b0 M n q y * f y| ≤ ∑ y, |histo b0 M n q y * f y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, histo b0 M n q y * |f y| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (histo_nonneg _ _ _ _ _)]
      _ ≤ ∑ y, ((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
            (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n)) / 3 ^ q * |f y| :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hpt y) (abs_nonneg _)
      _ = _ := by unfold normL1; rw [← Finset.mul_sum]; ring
  have hG := one_le_Gc
  have hGn : 1 ≤ Gc ^ n := one_le_pow₀ hG
  have hGn0 : 0 ≤ Gc ^ n := by positivity
  have hMs := Mstar_le hb1 n
  have hK : (Kstar n : ℝ) ≤ n * n := by exact_mod_cast Kstar_le n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb0' : (0 : ℝ) ≤ b0 := Nat.cast_nonneg b0
  have h916 : (9 / 16 : ℝ) ^ bseq b0 n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h16 : (0 : ℝ) < 16 ^ b0 := by positivity
  have hC1 : 2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n ≤ 2 ^ (b0 + 1) + 16 ^ b0 := by
    nlinarith
  have hA : 2 * (Mstar b0 n : ℝ) + 1 ≤ (3 + 2 * b0) * (n + 1) * Gc ^ n := by
    have ha : (n + 1 : ℝ) ≤ (n + 1) * Gc ^ n := by nlinarith
    have hb : (b0 : ℝ) * n * Gc ^ n ≤ b0 * (n + 1) * Gc ^ n := by
      have := mul_nonneg hb0' hGn0
      nlinarith
    nlinarith
  have hB : (Kstar n : ℝ) + 4 * n + 1 ≤ 5 * (n + 1) ^ 2 := by nlinarith
  have hR : ((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
      (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n)) ≤
      ((3 + 2 * b0) * (n + 1) * Gc ^ n) * (5 * (n + 1) ^ 2) * (2 ^ (b0 + 1) + 16 ^ b0) := by
    have p1 : (0 : ℝ) ≤ 2 * Mstar b0 n + 1 := by positivity
    have p2 : (0 : ℝ) ≤ Kstar n + 4 * n + 1 := by positivity
    have p3 : (0 : ℝ) ≤ 2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n := by positivity
    exact mul_le_mul (mul_le_mul hA hB p2 (by positivity)) hC1 p3 (by positivity)
  calc |∑ y, histo b0 M n q y * f y|
      ≤ ((2 * Mstar b0 n + 1) * (Kstar n + 4 * n + 1) *
          (2 ^ (b0 + 1) + 16 ^ b0 * (9 / 16 : ℝ) ^ bseq b0 n)) * normL1 q f := h1
    _ ≤ (((3 + 2 * b0) * (n + 1) * Gc ^ n) * (5 * (n + 1) ^ 2) * (2 ^ (b0 + 1) + 16 ^ b0)) *
          normL1 q f := mul_le_mul_of_nonneg_right hR (normL1_nonneg q f)
    _ = 5 * (3 + 2 * b0) * (2 ^ (b0 + 1) + 16 ^ b0) * (n + 1) ^ 3 * Gc ^ n * normL1 q f := by
        ring

end Positivity
end CollatzCLT
