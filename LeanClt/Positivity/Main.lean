import LeanClt.Positivity.Terminal
import LeanClt.Positivity.Seed
import LeanClt.Elementary.Syracuse

/-!
# §8.5: removing the mark and counting distinct sources; Theorem 8.1

**Credit.** Theorem 8.1 (positive lower density of `P_T(a)` for `3 ∤ a`) is due to L. Mazur,
*Positive lower density of Collatz predecessors* (2026), building on his *Explicit
positive-density Collatz convergence in logarithmic time* (2026); priority for the result rests
with him. The proof formalized in `Positivity/` follows his strategy and construction, with
Tao's Proposition 1.14 as its only input. See the README.

**Theorem 8.1 [`thm:positivity`]** is `positivity_of_offsetMixing` (from (8.1, `eq:A1`)) and
`positivity_of_tao` (from Tao's two imports). The proof is the paper's (§8.5):

* **The reduction.** Lowering the outermost letter of a terminal word by an even number `2j`
  until the overshoot is `0` or `1` keeps the word terminal and the letter `≥ 1`
  (`firstCross_reduce`, `terminal_reduce`); realisability is unchanged and the original source is
  `Ψ_j(x) = 4^j x + (4^j - 1)/3` (`realizes_reduce`, `src_reduce`, Lemma 8.2 [`lem:realisable`]),
  with weight `4^{-j}` times the reduced weight (`wt_raise`).
* **The fan.** The marked mass of the terminal words at one endpoint is at most the sum, over the
  reduced words, of the fan weights `4^{-j} ρ_{k_n}(Ψ_j(x))`, `j ≤ K_n` (`sum_mark_le_fan`), so the
  terminal marked mass is at most the corresponding sum over the reduced histories (`redPairs`,
  `termMass_le_fan`).
* **(8.10, `eq:F1`) and the paragraph after it.** Every reduced source lies in `[X, 32X)` (`redSrc_bounds`, from (8.5) for
  terminal blocks with overshoot `≤ 1`), carries weight at most `M/x` (`redWt_mul_le`), lies in
  `P_T(a)` (`redSrc_mem`), and distinct reduced histories give distinct sources (`redSrc_injOn`:
  the source reaches the nonperiodic seed at one depth, the word is then determined, and the cuts
  are determined by the word, `flatten_append_inj`).
* **The coarse/fine split** with (8.1) at `A = 2` and the count of each residue class modulo
  `3^{k_n}` in `[X, 32X)` (`fine_sum_le`; `Ψ_j` permutes `G_{k_n}`, `sum_psi_eq`), giving
  `𝒰 ≥ 9a₀/(16·3^{m₀})` and at least `X𝒰/M` distinct sources (`count_at_scale`).

Choices are made in the paper's order: `b₀`, then `a₀`, `n₁` and the class `y mod 3^Q`
(`terminal_mass`), then the seed `M` in that class (Lemma 8.7 [`lem:seed`], `seed`), then `m₀`, then
`X` large, with `n ≥ max n₁ m₀` from Lemma 8.8 [`lem:allscales`] (`allscales_of_bounds`), so that
`k_n ≥ m₀` (`le_kseq`).
-/

open Finset Real Filter Function

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## The reduction of the terminal overshoot -/

/-- `Ψ_j(x) = 4^j x + (4^j - 1)/3`. -/
def psi (j x : ℕ) : ℕ := 4 ^ j * x + (4 ^ j - 1) / 3

/-- Raise the outermost letter of a word by `2j` (the inverse of the reduction). -/
def raise (p : Word × ℕ) : Word := p.1.dropLast ++ [p.1.getLastD 0 + 2 * p.2]

lemma raise_concat (v : Word) (a j : ℕ) : raise (v ++ [a], j) = v ++ [a + 2 * j] := by
  simp [raise]

lemma pre_concat_of_le {v : Word} {a j : ℕ} (hj : j ≤ v.length) : pre (v ++ [a]) j = pre v j := by
  unfold pre; rw [List.take_append_of_le_length hj]

lemma tot_concat (v : Word) (a : ℕ) : tot (v ++ [a]) = tot v + a := by
  simp [tot]

lemma pos_concat {v : Word} {a : ℕ} (hv : v.Pos) (ha : 1 ≤ a) : (v ++ [a]).Pos := fun x hx => by
  rcases List.mem_append.mp hx with hx | hx
  · exact hv x hx
  · rw [List.mem_singleton.mp hx]; exact ha

lemma pos_append {u v : Word} (hu : u.Pos) (hv : v.Pos) : (u ++ v).Pos := fun x hx => by
  rcases List.mem_append.mp hx with hx | hx
  · exact hu x hx
  · exact hv x hx

/-- **The reduction** (§8.5): a first-crossing word for a nondecreasing barrier is obtained from
a first-crossing word with overshoot `≤ 1` by raising its outermost letter by `2j ≤ K`; the
lowered letter is `≥ 1`, because the previous partial sum is strictly below the barrier. -/
lemma firstCross_reduce {l : ℕ} {Hs : ℕ → ℤ} (hmono : ∀ s, Hs s ≤ Hs (s + 1)) {K : ℕ} {w : Word}
    (h : FirstCross l Hs K w) :
    ∃ (v : Word) (a j : ℕ), 1 ≤ a ∧ 2 * j ≤ K ∧ FirstCross l Hs 1 (v ++ [a]) ∧
      w = v ++ [a + 2 * j] := by
  obtain ⟨hpos, hl, hbelow, hge, hle⟩ := h
  rcases List.eq_nil_or_concat w with hw | ⟨v, c, rfl⟩
  · subst hw; simp at hl
  rw [List.concat_eq_append] at hpos hl hbelow hge hle ⊢
  have hlen : (v ++ [c]).length = v.length + 1 := by simp
  rw [hlen] at hl hge hle hbelow
  have hprev := hbelow v.length (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [pre_concat_of_le le_rfl, pre_length] at hprev
  rw [← hlen, pre_length, tot_concat, hlen] at hge hle
  have hm := hmono v.length
  have hvpos : Word.Pos v := fun x hx => hpos x (List.mem_append_left _ hx)
  obtain ⟨o, ho⟩ := Int.eq_ofNat_of_zero_le
    (show (0 : ℤ) ≤ ((tot v + c : ℕ) : ℤ) - Hs (v.length + 1) by omega)
  refine ⟨v, c - 2 * (o / 2), o / 2, by omega, by omega, ⟨pos_concat hvpos (by omega), ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · simp; omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hj'
    rw [pre_concat_of_le hj'.2]
    have := hbelow j (Finset.mem_Icc.mpr ⟨hj'.1, by omega⟩)
    rwa [pre_concat_of_le hj'.2] at this
  · rw [pre_length, tot_concat]; simp only [List.length_append, List.length_singleton]; push_cast
    omega
  · rw [pre_length, tot_concat]; simp only [List.length_append, List.length_singleton]; push_cast
    omega
  · congr 2; omega

/-- **The reduction for terminal blocks**: a terminal block with overshoot `≤ K` is a terminal
block with overshoot `≤ 1` (same shift) whose outermost letter is raised by `2j`, `j ≤ K`. -/
lemma terminal_reduce {b K u : ℕ} {w : Word} (hw : w ∈ terminal b K u) :
    ∃ (v : Word) (a j : ℕ), 1 ≤ a ∧ j < K + 1 ∧ v ++ [a] ∈ terminal b 1 u ∧
      w = v ++ [a + 2 * j] := by
  obtain ⟨hfc, hlen⟩ := isTerminal_iff.mp (mem_terminal.mp hw)
  obtain ⟨v, a, j, ha, hj, hfc', rfl⟩ :=
    firstCross_reduce (fun s => tbar_mono b u (Nat.le_succ s)) hfc
  refine ⟨v, a, j, ha, by omega, mem_terminal.mpr (isTerminal_iff.mpr ⟨hfc', ?_⟩), rfl⟩
  simpa using hlen

/-- A terminal block is a positive word followed by an outermost letter `≥ 1`. -/
lemma concat_of_terminal {b K u : ℕ} {w : Word} (hw : w ∈ terminal b K u) :
    ∃ (v : Word) (a : ℕ), v.Pos ∧ 1 ≤ a ∧ w = v ++ [a] := by
  obtain ⟨⟨hpos, hl, -⟩, -⟩ := isTerminal_iff.mp (mem_terminal.mp hw)
  rcases List.eq_nil_or_concat w with hw' | ⟨v, c, rfl⟩
  · subst hw'; simp at hl
  rw [List.concat_eq_append] at hpos ⊢
  exact ⟨v, c, fun x hx => hpos x (List.mem_append_left _ hx), hpos c (by simp), rfl⟩

/-- Raising the outermost letter by `2j` multiplies the weight by `4^{-j}`. -/
lemma wt_raise (v : Word) (a j : ℕ) : wt (v ++ [a + 2 * j]) = (1 / 4) ^ j * wt (v ++ [a]) := by
  unfold wt gm
  rw [tot_concat, tot_concat]
  have e : (1 / 2 : ℝ) ^ (tot v + (a + 2 * j)) = (1 / 4) ^ j * (1 / 2) ^ (tot v + a) := by
    rw [show tot v + (a + 2 * j) = (tot v + a) + 2 * j by ring, pow_add, pow_mul]
    norm_num
    ring
  simp only [List.length_append, List.length_singleton]
  rw [e]
  ring

/-! ## The fan at one endpoint -/

lemma rhoX_nonneg (q : ℕ) (y : ZMod (3 ^ q)) : 0 ≤ rhoX q y := by
  unfold rhoX; have := lawX_nonneg q y; positivity

lemma lawX_le_one (q : ℕ) (y : ZMod (3 ^ q)) : lawX q y ≤ 1 := by
  rw [← sum_lawX q]
  exact Finset.single_le_sum (fun z _ => lawX_nonneg q z) (Finset.mem_univ y)

/-- `ρ_q ≤ (2/3) 3^q`. -/
lemma rhoX_le (q : ℕ) (y : ZMod (3 ^ q)) : rhoX q y ≤ 2 / 3 * 3 ^ q := by
  unfold rhoX
  have := lawX_le_one q y
  have h : (0 : ℝ) ≤ 2 / 3 * 3 ^ q := by positivity
  nlinarith

open Classical in
/-- The marked contribution of one terminal word at the endpoint `R`. -/
def mark (k R : ℕ) (w : Word) : ℝ := if Realizes w R then wt w * rhoX k (src w R) else 0

open Classical in
/-- The fan of a reduced word at the endpoint `R`: `W(w) ∑_{j<J} 4^{-j} ρ_k(Ψ_j(x))`, `x` its
source. -/
def fan (k R J : ℕ) (w : Word) : ℝ :=
  if Realizes w R then wt w * ∑ j ∈ range J, (1 / 4 : ℝ) ^ j * rhoX k (psi j (src w R)) else 0

lemma mark_nonneg (k R : ℕ) (w : Word) : 0 ≤ mark k R w := by
  unfold mark
  split_ifs
  · exact mul_nonneg (wt_pos w).le (rhoX_nonneg _ _)
  · exact le_rfl

open Classical in
lemma mark_raise {v : Word} (hv : v.Pos) {a : ℕ} (ha : 1 ≤ a) {R : ℕ} (hR : Odd R) (k j : ℕ) :
    mark k R (v ++ [a + 2 * j]) = if Realizes (v ++ [a]) R then
      wt (v ++ [a]) * ((1 / 4 : ℝ) ^ j * rhoX k (psi j (src (v ++ [a]) R))) else 0 := by
  unfold mark
  by_cases hr : Realizes (v ++ [a]) R
  · have h' := (realizes_reduce v a j R).mpr hr
    simp only [h', hr, ↓reduceIte]
    rw [wt_raise, src_reduce hv ha j hR hr]
    unfold psi
    ring
  · have h' : ¬ Realizes (v ++ [a + 2 * j]) R := fun h => hr ((realizes_reduce v a j R).mp h)
    simp only [h', hr, ↓reduceIte]

/-- **The fan bound at one endpoint** (§8.5): the marked mass of the terminal words with
overshoot `≤ K` is at most the fan sum over the terminal words with overshoot `≤ 1`. Every
original word is a raised reduced word (`terminal_reduce`), so summing over the image of `raise`
needs no injectivity. -/
theorem sum_mark_le_fan (k : ℕ) {R : ℕ} (hR : Odd R) (b K u : ℕ) :
    ∑ w ∈ terminal b K u, mark k R w ≤ ∑ w ∈ terminal b 1 u, fan k R (K + 1) w := by
  classical
  calc ∑ w ∈ terminal b K u, mark k R w
      ≤ ∑ w ∈ (terminal b 1 u ×ˢ range (K + 1)).image raise, mark k R w := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro w hw
          obtain ⟨v, a, j, -, hj, hva, rfl⟩ := terminal_reduce hw
          exact Finset.mem_image.mpr ⟨(v ++ [a], j),
            Finset.mem_product.mpr ⟨hva, Finset.mem_range.mpr hj⟩, raise_concat v a j⟩
        · intro w _ _; exact mark_nonneg k R w
    _ ≤ ∑ p ∈ terminal b 1 u ×ˢ range (K + 1), mark k R (raise p) :=
        Finset.sum_image_le_of_nonneg fun w _ => mark_nonneg k R w
    _ = ∑ w ∈ terminal b 1 u, ∑ j ∈ range (K + 1), mark k R (raise (w, j)) :=
        Finset.sum_product _ _ _
    _ = ∑ w ∈ terminal b 1 u, fan k R (K + 1) w := by
        refine Finset.sum_congr rfl fun w hw => ?_
        obtain ⟨v, a, hv, ha, rfl⟩ := concat_of_terminal hw
        simp only [raise_concat]
        rw [Finset.sum_congr rfl fun j _ => mark_raise hv ha hR k j]
        unfold fan
        split_ifs with hr
        · rw [Finset.mul_sum]
        · simp

/-! ## Reduced histories -/

/-- A history together with a terminal word. -/
abbrev RPair := Σ _ : List Word, Word

open Classical in
/-- The **reduced histories** at generation `n` and scale `X`: a history `H` from `M` followed by a
terminal block with overshoot `≤ 1` at the selected shift of its endpoint, realisable there. -/
def redPairs (b0 M n : ℕ) (X : ℝ) : Finset RPair :=
  (hist b0 M n).sigma fun H =>
    (terminal (bseq b0 n) 1 (shiftOf (bseq b0 n) (endpt M H) X)).filter
      fun w => Realizes w (endpt M H)

/-- The source of a reduced history. -/
def redSrc (M : ℕ) (p : RPair) : ℕ := src p.2 (endpt M p.1)

/-- The weight of a reduced history. -/
def redWt (p : RPair) : ℝ := wt p.1.flatten * wt p.2

lemma redWt_nonneg (p : RPair) : 0 ≤ redWt p :=
  mul_nonneg (wt_pos _).le (wt_pos _).le

lemma mem_redPairs {b0 M n : ℕ} {X : ℝ} {p : RPair} (hp : p ∈ redPairs b0 M n X) :
    p.1 ∈ hist b0 M n ∧ p.2 ∈ terminal (bseq b0 n) 1 (shiftOf (bseq b0 n) (endpt M p.1) X) ∧
      Realizes p.2 (endpt M p.1) := by
  classical
  unfold redPairs at hp
  rw [Finset.mem_sigma, Finset.mem_filter] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2⟩

/-- **The terminal marked mass is at most the fan sum over reduced histories** (§8.5). -/
theorem termMass_le_fan (b0 : ℕ) {M : ℕ} (hM : Odd M) (n : ℕ) (X : ℝ) :
    termMass b0 M n X ≤ ∑ p ∈ redPairs b0 M n X, redWt p *
      ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * rhoX (kseq b0 n) (psi j (redSrc M p)) := by
  classical
  have e : termMass b0 M n X = ∑ H ∈ hist b0 M n, wt H.flatten *
      ∑ w ∈ terminal (bseq b0 n) (Kseq n) (shiftOf (bseq b0 n) (endpt M H) X),
        mark (kseq b0 n) (endpt M H) w := rfl
  rw [e]
  unfold redPairs
  rw [Finset.sum_sigma]
  refine Finset.sum_le_sum fun H hH => ?_
  have hR := endpt_odd hM hH
  calc wt H.flatten * ∑ w ∈ terminal (bseq b0 n) (Kseq n) (shiftOf (bseq b0 n) (endpt M H) X),
        mark (kseq b0 n) (endpt M H) w
      ≤ wt H.flatten * ∑ w ∈ terminal (bseq b0 n) 1 (shiftOf (bseq b0 n) (endpt M H) X),
        fan (kseq b0 n) (endpt M H) (Kseq n + 1) w :=
        mul_le_mul_of_nonneg_left (sum_mark_le_fan _ hR _ _ _) (wt_pos _).le
    _ = _ := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        unfold fan redWt redSrc
        split_ifs
        · ring
        · simp

/-! ## (8.10): the reduced sources, their weights and their distinctness -/

lemma two_pow_succ_le_endpt {b0 : ℕ} (hb0 : 100 ≤ b0) {M n : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    {H : List Word} (hH : H ∈ hist b0 M n) : (2 : ℝ) ^ (bseq b0 n + 1) ≤ endpt M H := by
  have h1 := endpt_ge hb0 hM hM16 hH
  have hb : 1 ≤ bseq b0 n := le_trans (by omega) (le_bseq b0 n)
  have h2 : (2 : ℝ) ^ (bseq b0 n + 2) ≤ 16 ^ bseq b0 n := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (bseq b0 n + 2) = 2 * 2 ^ (bseq b0 n + 1) := by rw [pow_succ]; ring
  linarith

/-- **(8.10, `eq:F1`)**: every reduced source `x` satisfies `X ≤ x < 32X`, by (8.5) for terminal
blocks with overshoot `≤ 1` and `X ≤ 2^u L_b(R) < 2X`. -/
theorem redSrc_bounds {b0 : ℕ} (hb0 : 100 ≤ b0) {M n : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    {X : ℝ} (hX : Admissible b0 M n X) {p : RPair} (hp : p ∈ redPairs b0 M n X) :
    X ≤ redSrc M p ∧ (redSrc M p : ℝ) < 32 * X := by
  obtain ⟨hH, hw, hr⟩ := mem_redPairs hp
  have hRo := endpt_odd hM hH
  have h2R := two_pow_succ_le_endpt hb0 hM hM16 hH
  obtain ⟨hL, hU⟩ := hX p.1 hH
  obtain ⟨-, -, hs1, hs2⟩ := shiftOf_spec hRo.pos hL hU
  obtain ⟨hp1, hp2⟩ := phi_bounds_terminal hw h2R
  have e := (realisable_of_realizes (mem_terminal.mp hw).1.1 hRo hr).1
  have hsrc : (src p.2 (endpt M p.1) : ℝ) = ((Phi p.2 (endpt M p.1) : ℚ) : ℝ) := by
    rw [← e, Rat.cast_natCast]
  unfold redSrc
  rw [hsrc]
  have h16 : (2 : ℝ) ^ (shiftOf (bseq b0 n) (endpt M p.1) X + 1 + 3) =
      16 * 2 ^ shiftOf (bseq b0 n) (endpt M p.1) X := by
    rw [pow_add, pow_add]; ring
  rw [h16] at hp2
  constructor <;> nlinarith [Lb_pos (b := bseq b0 n) hRo.pos]

/-- The affine identity gives `x W ≤ M` for a reduced source `x` of weight `W`. -/
theorem redWt_mul_le {b0 M n : ℕ} (hM : Odd M) {X : ℝ} {p : RPair}
    (hp : p ∈ redPairs b0 M n X) : redWt p * redSrc M p ≤ M := by
  obtain ⟨hH, hw, hr⟩ := mem_redPairs hp
  obtain ⟨hHb, hHr⟩ := mem_hist.mp hH
  have hRo := endpt_odd hM hH
  have e1 := wt_mul_src_add (flatten_pos (mem_blocks.mp hHb).2) hM hHr
  have e2 := wt_mul_src_add (mem_terminal.mp hw).1.1 hRo hr
  have t1 : (0 : ℝ) ≤ thetaW p.1.flatten := by exact_mod_cast thetaW_nonneg _
  have t2 : (0 : ℝ) ≤ thetaW p.2 := by exact_mod_cast thetaW_nonneg _
  have hw1 : wt p.2 * (src p.2 (endpt M p.1) : ℝ) ≤ endpt M p.1 := by linarith
  have hw2 := mul_le_mul_of_nonneg_left hw1 (wt_pos p.1.flatten).le
  unfold endpt at e1 hw2
  unfold redWt redSrc endpt
  nlinarith

/-- Every reduced source reaches the seed, hence lies in `P_T(a)`. -/
theorem redSrc_mem {b0 M n a : ℕ} (hM : Odd M) (hMa : M ∈ Pred T a) {X : ℝ} {p : RPair}
    (hp : p ∈ redPairs b0 M n X) : redSrc M p ∈ Pred T a := by
  obtain ⟨hH, hw, hr⟩ := mem_redPairs hp
  obtain ⟨hHb, hHr⟩ := mem_hist.mp hH
  have hRo := endpt_odd hM hH
  obtain ⟨-, hxo, -, hU2⟩ := realisable_of_realizes (mem_terminal.mp hw).1.1 hRo hr
  obtain ⟨-, -, -, hU1⟩ := realisable_of_realizes (flatten_pos (mem_blocks.mp hHb).2) hM hHr
  obtain ⟨m, hm⟩ := exists_T_iterate_eq_U_iterate hxo (p.1.flatten.length + p.2.length)
  obtain ⟨-, k, hk⟩ := hMa
  refine ⟨hxo.pos, k + m, ?_⟩
  unfold redSrc
  rw [iterate_add_apply, hm, iterate_add_apply, hU2]
  unfold endpt
  rw [hU1, hk]

/-- **The cuts are determined by the word**, for a run of blocks from prefix-free families
followed by one more word. -/
theorem flatten_append_inj {V : ℕ → Finset Word} (hV : ∀ j, PrefixFree (V j)) :
    ∀ (H H' : List Word) (w w' : Word), H.length = H'.length →
      (∀ j (h : j < H.length), H[j] ∈ V j) → (∀ j (h : j < H'.length), H'[j] ∈ V j) →
      H.flatten ++ w = H'.flatten ++ w' → H = H' ∧ w = w' := by
  intro H
  induction H generalizing V with
  | nil =>
    intro H' w w' hl _ _ hf
    have hH' : H' = [] := (List.eq_nil_of_length_eq_zero hl.symm)
    subst hH'
    exact ⟨rfl, by simpa using hf⟩
  | cons v H ih =>
    intro H' w w' hl hH hH' hf
    obtain ⟨v', H₁', rfl⟩ := List.exists_cons_of_length_pos (by simp at hl; omega : 0 < H'.length)
    rw [List.flatten_cons, List.flatten_cons, List.append_assoc, List.append_assoc] at hf
    have hv := hH 0 (by simp)
    have hv' := hH' 0 (by simp)
    simp only [List.getElem_cons_zero] at hv hv'
    have p1 : v <+: v' ++ (H₁'.flatten ++ w') := hf ▸ List.prefix_append v (H.flatten ++ w)
    have p2 : v' <+: v' ++ (H₁'.flatten ++ w') := List.prefix_append _ _
    have hvv' : v = v' := by
      rcases le_total v.length v'.length with hle | hle
      · exact hV 0 v hv v' hv' (List.prefix_of_prefix_length_le p1 p2 hle)
      · exact (hV 0 v' hv' v hv (List.prefix_of_prefix_length_le p2 p1 hle)).symm
    subst hvv'
    obtain ⟨h1, h2⟩ := ih (V := fun j => V (j + 1)) (fun j => hV (j + 1)) H₁' w w'
      (by simpa using hl)
      (fun j h => by
        have := hH (j + 1) (by simp; omega)
        rwa [List.getElem_cons_succ] at this)
      (fun j h => by
        have := hH' (j + 1) (by simp; omega)
        rwa [List.getElem_cons_succ] at this)
      (List.append_cancel_left hf)
    exact ⟨by rw [h1], h2⟩

/-- **Distinct reduced histories give distinct sources** (§8.5): a source hits the nonperiodic
seed `M` at one depth only, its valuation word is then determined, and the word determines the
cuts. -/
theorem redSrc_injOn {b0 M n : ℕ} (hM : Odd M) (hper : ∀ q, 0 < q → U^[q] M ≠ M) (X : ℝ) :
    Set.InjOn (redSrc M) (redPairs b0 M n X) := by
  rintro ⟨H1, w1⟩ hp1 ⟨H2, w2⟩ hp2 he
  obtain ⟨hH1, hw1, hr1⟩ := mem_redPairs hp1
  obtain ⟨hH2, hw2, hr2⟩ := mem_redPairs hp2
  obtain ⟨hb1, hR1⟩ := mem_hist.mp hH1
  obtain ⟨hb2, hR2⟩ := mem_hist.mp hH2
  obtain ⟨hl1, ht1⟩ := mem_blocks.mp hb1
  obtain ⟨hl2, ht2⟩ := mem_blocks.mp hb2
  have hP1 := flatten_pos ht1
  have hP2 := flatten_pos ht2
  have hq1 := (mem_terminal.mp hw1).1.1
  have hq2 := (mem_terminal.mp hw2).1.1
  have hF1 : Realizes (H1.flatten ++ w1) M := (realizes_append hP1 hM).mpr ⟨hR1, hr1⟩
  have hF2 : Realizes (H2.flatten ++ w2) M := (realizes_append hP2 hM).mpr ⟨hR2, hr2⟩
  have hs1 := src_append hP1 hq1 hM hF1
  have hs2 := src_append hP2 hq2 hM hF2
  have hF := word_unique hM hper (pos_append hP1 hq1) (pos_append hP2 hq2) hF1 hF2
    (by rw [hs1, hs2]; exact he)
  obtain ⟨rfl, rfl⟩ := flatten_append_inj (V := fun j => central (bseq b0 j) (Kseq j))
    (fun j => central_prefixFree _ _) H1 H2 w1 w2 (hl1.trans hl2.symm)
    (fun j h => by simpa using ht1 j h) (fun j h => by simpa using ht2 j h) hF
  rfl

/-! ## Counting residue classes in `[X, 32X)` -/

/-- A nonnegative function of the residue mod `3^k`, summed over `[A, B]`, is at most
`⌊(B - A)/3^k⌋ + 1` times its sum over `G_k`. -/
lemma sum_Icc_le (k A B : ℕ) (f : ZMod (3 ^ k) → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ x ∈ Icc A B, f x ≤ (((B - A) / 3 ^ k + 1 : ℕ) : ℝ) * ∑ z, f z := by
  rw [← Finset.sum_fiberwise (Icc A B) (fun x : ℕ => (x : ZMod (3 ^ k))) (fun x => f x),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const,
    nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hf z)
  have hfil : (Icc A B).filter (fun x : ℕ => (x : ZMod (3 ^ k)) = z) =
      (Icc A B).filter (fun x => x ≡ z.val [MOD 3 ^ k]) := by
    refine Finset.filter_congr fun x _ => ?_
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact ZMod.natCast_eq_natCast_iff _ _ _
  rw [hfil]
  exact_mod_cast card_filter_modEq_le A B (3 ^ k) z.val

lemma psi_cast (k j x : ℕ) : ((psi j x : ℕ) : ZMod (3 ^ k)) =
    4 ^ j * (x : ZMod (3 ^ k)) + (((4 ^ j - 1) / 3 : ℕ) : ZMod (3 ^ k)) := by
  simp only [psi, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- `Ψ_j` permutes `G_k` (`4` is a unit mod `3^k`). -/
lemma sum_psi_eq (k j c : ℕ) (f : ZMod (3 ^ k) → ℝ) :
    ∑ z, f (4 ^ j * z + (c : ZMod (3 ^ k))) = ∑ z, f z := by
  have hu : IsUnit ((4 : ZMod (3 ^ k)) ^ j) := by
    have : (4 : ZMod (3 ^ k)) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]; exact (isUnit_two_zmod k).pow _
  have := Equiv.sum_comp ((Units.mulLeft hu.unit).trans (Equiv.addRight (c : ZMod (3 ^ k)))) f
  simpa using this

/-- **The count in `[X, 32X)`**: for `3^k ≤ X`, a nonnegative function of the residue of the
reduced source mod `3^k`, summed over the reduced histories, is at most `32X/3^k` times its sum
over `G_k`; the reduced sources are distinct and lie in `[X, 32X)`. -/
theorem fine_sum_le {b0 : ℕ} (hb0 : 100 ≤ b0) {M n : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    (hper : ∀ q, 0 < q → U^[q] M ≠ M) {X : ℝ} (hX : Admissible b0 M n X) {k : ℕ}
    (hk : (3 : ℝ) ^ k ≤ X) (g : ZMod (3 ^ k) → ℝ) (hg : ∀ z, 0 ≤ g z) :
    ∑ p ∈ redPairs b0 M n X, g (redSrc M p) ≤ 32 * X / 3 ^ k * ∑ z, g z := by
  classical
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le h3k hk
  have himg : (redPairs b0 M n X).image (redSrc M) ⊆ Icc ⌈X⌉₊ ⌊32 * X⌋₊ := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2⟩ := redSrc_bounds hb0 hM hM16 hX hp
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2.le⟩
  have hBA : (((⌊32 * X⌋₊ - ⌈X⌉₊ : ℕ)) : ℝ) ≤ 31 * X := by
    rcases le_total ⌈X⌉₊ ⌊32 * X⌋₊ with h | h
    · rw [Nat.cast_sub h]
      have := Nat.floor_le (show 0 ≤ 32 * X by linarith)
      have := Nat.le_ceil X
      linarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; linarith
  have hN : (((⌊32 * X⌋₊ - ⌈X⌉₊) / 3 ^ k + 1 : ℕ) : ℝ) ≤ 32 * X / 3 ^ k := by
    have h1 : (((⌊32 * X⌋₊ - ⌈X⌉₊) / 3 ^ k : ℕ) : ℝ) ≤
        ((⌊32 * X⌋₊ - ⌈X⌉₊ : ℕ) : ℝ) / ((3 ^ k : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at h1 ⊢
    have h2 : ((⌊32 * X⌋₊ - ⌈X⌉₊ : ℕ) : ℝ) / 3 ^ k ≤ 31 * X / 3 ^ k :=
      div_le_div_of_nonneg_right hBA h3k.le
    have h3 : (1 : ℝ) ≤ X / 3 ^ k := (one_le_div h3k).mpr hk
    have h4 : 31 * X / 3 ^ k + X / 3 ^ k = 32 * X / 3 ^ k := by ring
    linarith
  calc ∑ p ∈ redPairs b0 M n X, g (redSrc M p)
      = ∑ x ∈ (redPairs b0 M n X).image (redSrc M), g x :=
        (Finset.sum_image (f := fun x : ℕ => g (x : ZMod (3 ^ k))) (redSrc_injOn hM hper X)).symm
    _ ≤ ∑ x ∈ Icc ⌈X⌉₊ ⌊32 * X⌋₊, g x :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun x _ _ => hg _
    _ ≤ (((⌊32 * X⌋₊ - ⌈X⌉₊) / 3 ^ k + 1 : ℕ) : ℝ) * ∑ z, g z := sum_Icc_le k _ _ g hg
    _ ≤ 32 * X / 3 ^ k * ∑ z, g z :=
        mul_le_mul_of_nonneg_right hN (Finset.sum_nonneg fun z _ => hg z)

/-! ## The count at one scale -/

lemma geom_quarter_le (J : ℕ) : ∑ j ∈ range J, (1 / 4 : ℝ) ^ j ≤ 4 / 3 := by
  have h := geom_sum_mul (1 / 4 : ℝ) J
  have h0 : (0 : ℝ) ≤ (1 / 4) ^ J := by positivity
  nlinarith

lemma geom_quarter_nonneg (J : ℕ) : 0 ≤ ∑ j ∈ range J, (1 / 4 : ℝ) ^ j :=
  Finset.sum_nonneg fun j _ => by positivity

lemma eight_mul_nine_pow_le {b : ℕ} (hb : 4 ≤ b) : 8 * 9 ^ b ≤ 16 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    calc 8 * 9 ^ (m + 1) = 9 * (8 * 9 ^ m) := by ring
      _ ≤ 9 * 16 ^ m := Nat.mul_le_mul_left 9 ih
      _ ≤ 16 * 16 ^ m := Nat.mul_le_mul_right _ (by norm_num)
      _ = 16 ^ (m + 1) := by ring

/-- `3^{k_n} ≤ L_{b_n}(R)` at endpoints `R ≥ 16^{b_n}/2`; with `L_{b_n}(R) < X`, `3^{k_n} ≤ X`. -/
lemma three_pow_le_Lb {b R : ℕ} (hb : 4 ≤ b) (hR : (16 : ℝ) ^ b / 2 ≤ R) :
    (3 : ℝ) ^ (b / 4) ≤ Lb b R := by
  unfold Lb
  have hr : (2 : ℝ) ^ rB b ≤ 4 ^ b := by
    have : rB b ≤ 2 * b := by unfold rB wB; omega
    calc (2 : ℝ) ^ rB b ≤ 2 ^ (2 * b) := pow_le_pow_right₀ (by norm_num) this
      _ = 4 ^ b := by rw [pow_mul]; norm_num
  have h89 : (8 : ℝ) * 9 ^ b ≤ 16 ^ b := by exact_mod_cast eight_mul_nine_pow_le hb
  have h3 : (3 : ℝ) ^ (b / 4) ≤ 3 ^ b := pow_le_pow_right₀ (by norm_num) (Nat.div_le_self _ _)
  have hA : (0 : ℝ) < 3 ^ b := by positivity
  have hB : (0 : ℝ) < 4 ^ b := by positivity
  have e9 : (9 : ℝ) ^ b = (3 ^ b) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e16 : (16 : ℝ) ^ b = (4 ^ b) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e9, e16] at h89
  rw [e16] at hR
  rw [le_div_iff₀ (by positivity), div_pow]
  have hc : (0 : ℝ) ≤ 3 ^ (b / 4) := by positivity
  have hr0 : (0 : ℝ) ≤ 2 ^ rB b := by positivity
  have hstep1 : (3 : ℝ) ^ (b / 4) * (4 * 2 ^ rB b) ≤ 3 ^ b * (4 * 4 ^ b) :=
    mul_le_mul h3 (by linarith) (by positivity) hA.le
  have hstep2 : (3 : ℝ) ^ b * (4 * 4 ^ b) ≤ 4 ^ b / 3 ^ b * R := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    nlinarith [mul_le_mul_of_nonneg_left hR hB.le]
  linarith

/-- **The count at one scale** (§8.5): if the terminal marked mass at an admissible `X` is at
least `a₀ > 0`, and `‖ρ_{k_n} - lift ρ_{m₀}‖_{L¹(G_{k_n})} ≤ E` with `(128/3) M E ≤ a₀/2`
(supplied by (8.1) at `A = 2` when `m₀ ≤ k_n`), then the reduced histories
give at least `9a₀ X/(16·3^{m₀} M)` distinct elements of `P_T(a) ∩ [1, Y]` for every `Y ≥ 32X`. -/
theorem count_at_scale {b0 : ℕ} (hb0 : 100 ≤ b0) {M a : ℕ} (hM : Odd M) (hM16 : 16 ^ b0 ≤ M)
    (hper : ∀ q, 0 < q → U^[q] M ≠ M) (hMa : M ∈ Pred T a) {n m0 : ℕ} {X a₀ E : ℝ}
    (hX : Admissible b0 M n X) (ha₀ : 0 < a₀) (hmass : a₀ ≤ termMass b0 M n X)
    (hE : normL1 (kseq b0 n) (fun y => rhoX (kseq b0 n) y - rhoX m0 (ZMod.cast y)) ≤ E)
    (hfine : 128 / 3 * M * E ≤ a₀ / 2) {Y : ℕ} (hY : 32 * X ≤ Y) :
    9 * a₀ / (16 * 3 ^ m0 * M) * X ≤ ((window (Pred T a) Y).card : ℝ) := by
  classical
  set k := kseq b0 n with hk
  set P := redPairs b0 M n X with hP
  -- the generation is nonempty, so `3^{k_n} ≤ X`
  obtain ⟨H0, hH0⟩ : (hist b0 M n).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (hist b0 M n) with h | h
    · exfalso
      have : termMass b0 M n X = 0 := by unfold termMass; rw [h, Finset.sum_empty]
      linarith
    · exact h
  have hb4 : 4 ≤ bseq b0 n := le_trans (by omega) (le_bseq b0 n)
  have h3k : (3 : ℝ) ^ k ≤ X :=
    (three_pow_le_Lb hb4 (endpt_ge hb0 hM hM16 hH0)).trans (hX H0 hH0).1.le
  have h3k0 : (0 : ℝ) < 3 ^ k := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le h3k0 h3k
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM.pos
  -- notation
  set d : ZMod (3 ^ k) → ℝ := fun z => |rhoX k z - rhoX m0 (ZMod.cast z)| with hd
  set G := ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j with hG
  set Ut := ∑ p ∈ P, redWt p with hUt
  have hG43 : G ≤ 4 / 3 := geom_quarter_le _
  have hG0 : 0 ≤ G := geom_quarter_nonneg _
  have hd0 : ∀ z, 0 ≤ d z := fun z => abs_nonneg _
  have hnrm0 : 0 ≤ normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y)) := by
    unfold normL1; exact div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) h3k0.le
  have hsumd : ∑ z, d z = 3 ^ k * normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y)) := by
    unfold normL1; field_simp; rfl
  -- coarse/fine split, pointwise
  have hsplit : ∀ p ∈ P, redWt p * ∑ j ∈ range (Kseq n + 1),
      (1 / 4 : ℝ) ^ j * rhoX k (psi j (redSrc M p)) ≤
      2 / 3 * 3 ^ m0 * G * redWt p + redWt p * ∑ j ∈ range (Kseq n + 1),
        (1 / 4 : ℝ) ^ j * d (psi j (redSrc M p)) := by
    intro p _
    have h1 : ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * rhoX k (psi j (redSrc M p)) ≤
        ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * (2 / 3 * 3 ^ m0 + d (psi j (redSrc M p))) := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := rhoX_le m0 (ZMod.cast ((psi j (redSrc M p) : ℕ) : ZMod (3 ^ k)))
      have := le_abs_self (rhoX k (psi j (redSrc M p)) -
        rhoX m0 (ZMod.cast ((psi j (redSrc M p) : ℕ) : ZMod (3 ^ k))))
      simp only [hd]
      linarith
    have h2 : ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * (2 / 3 * 3 ^ m0 + d (psi j (redSrc M p))) =
        2 / 3 * 3 ^ m0 * G + ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * d (psi j (redSrc M p)) := by
      rw [hG, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have := mul_le_mul_of_nonneg_left (h1.trans h2.le) (redWt_nonneg p)
    linarith
  -- the fine part
  have hfine_j : ∀ j, ∑ p ∈ P, d (psi j (redSrc M p)) ≤
      32 * X * normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y)) := by
    intro j
    have h1 : ∀ p ∈ P, d (psi j (redSrc M p)) =
        (fun z => d (4 ^ j * z + (((4 ^ j - 1) / 3 : ℕ) : ZMod (3 ^ k)))) (redSrc M p) := by
      intro p _; simp only [psi_cast]
    rw [Finset.sum_congr rfl h1]
    have h2 := fine_sum_le hb0 hM hM16 hper hX h3k
      (fun z => d (4 ^ j * z + (((4 ^ j - 1) / 3 : ℕ) : ZMod (3 ^ k)))) (fun z => hd0 _)
    rw [sum_psi_eq k j ((4 ^ j - 1) / 3) d, hsumd] at h2
    calc _ ≤ 32 * X / 3 ^ k * (3 ^ k * normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y))) := h2
      _ = _ := by field_simp
  have hW : ∀ p ∈ P, redWt p ≤ M / X := by
    intro p hp
    have h1 := redWt_mul_le hM hp
    have h2 := (redSrc_bounds hb0 hM hM16 hX hp).1
    rw [le_div_iff₀ hX0]
    nlinarith [redWt_nonneg p]
  have hfine_tot : ∑ p ∈ P, redWt p * ∑ j ∈ range (Kseq n + 1),
      (1 / 4 : ℝ) ^ j * d (psi j (redSrc M p)) ≤ 128 / 3 * M * E := by
    calc ∑ p ∈ P, redWt p * ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * d (psi j (redSrc M p))
        ≤ ∑ p ∈ P, M / X * ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * d (psi j (redSrc M p)) :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (hW p hp)
            (Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hd0 _))
      _ = M / X * ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j * ∑ p ∈ P, d (psi j (redSrc M p)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ ≤ M / X * ∑ j ∈ range (Kseq n + 1), (1 / 4 : ℝ) ^ j *
            (32 * X * normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y))) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hfine_j j) (by positivity)) (by positivity)
      _ = M * G * 32 * normL1 k (fun y => rhoX k y - rhoX m0 (ZMod.cast y)) := by
          rw [← Finset.sum_mul, ← hG]; field_simp
      _ ≤ M * (4 / 3) * 32 * E := by
          have := mul_le_mul hG43 hE hnrm0 (by norm_num)
          nlinarith
      _ = 128 / 3 * M * E := by ring
  -- the mass inequality
  have hmass2 : a₀ ≤ 8 / 9 * 3 ^ m0 * Ut + a₀ / 2 := by
    have h1 := termMass_le_fan b0 hM n X
    have h2 := Finset.sum_le_sum hsplit
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    have h3 : 2 / 3 * 3 ^ m0 * G * Ut ≤ 8 / 9 * 3 ^ m0 * Ut := by
      have hU0 : 0 ≤ Ut := Finset.sum_nonneg fun p _ => redWt_nonneg p
      have : 2 / 3 * 3 ^ m0 * G ≤ 8 / 9 * 3 ^ m0 := by
        have h30 : (0 : ℝ) ≤ 3 ^ m0 := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right this hU0
    linarith
  -- the total reduced weight is at most `#P · M/X`
  have hUt : Ut ≤ P.card * (M / X) := by
    rw [hUt, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ hW
  -- `P` injects into `P_T(a) ∩ [1, Y]`
  have hcard : P.card ≤ (window (Pred T a) Y).card := by
    rw [← Finset.card_image_of_injOn (redSrc_injOn hM hper X)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2⟩ := redSrc_bounds hb0 hM hM16 hX hp
    unfold window
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, redSrc_mem hM hMa hp⟩
    · have : (0 : ℝ) < redSrc M p := lt_of_lt_of_le hX0 h1
      exact_mod_cast this
    · have : (redSrc M p : ℝ) ≤ Y := by linarith
      exact_mod_cast this
  have hcard' : (P.card : ℝ) ≤ (window (Pred T a) Y).card := by exact_mod_cast hcard
  -- combine
  have hU : 9 * a₀ / (16 * 3 ^ m0) ≤ Ut := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h30 : (0 : ℝ) < 3 ^ m0 := by positivity
  calc 9 * a₀ / (16 * 3 ^ m0 * M) * X = 9 * a₀ / (16 * 3 ^ m0) * (X / M) := by
        field_simp
    _ ≤ Ut * (X / M) := mul_le_mul_of_nonneg_right hU (by positivity)
    _ ≤ P.card * (M / X) * (X / M) := mul_le_mul_of_nonneg_right hUt (by positivity)
    _ = P.card := by field_simp
    _ ≤ _ := hcard'

/-! ## Theorem 8.1 -/

lemma le_kseq {b0 : ℕ} (hb0 : 1000000 ≤ b0) (n : ℕ) : n ≤ kseq b0 n := by
  have h := bseq_ge_lin hb0 n
  unfold kseq
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc n * 4 ≤ 10000 * n := by rw [mul_comm]; exact Nat.mul_le_mul_right n (by norm_num)
    _ ≤ 1000000 + 10000 * n := Nat.le_add_left _ _
    _ ≤ bseq b0 n := h

/-- **Theorem 8.1 [`thm:positivity`]**, from (8.1, `eq:A1`): for every positive integer `a` with
`3 ∤ a` there is `c > 0` with `#(P_T(a) ∩ [1, X]) ≥ c X` for all sufficiently large `X`. (v8 counts
`n < Y` for real `Y ≥ Y_a`; the two forms are equivalent up to halving `c`, since `0 ∉ P_T(a)`.) -/
theorem positivity_of_offsetMixing (hA1 : OffsetMixing) {a : ℕ} (ha : 0 < a) (h3 : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T a) X).card : ℝ) := by
  obtain ⟨b₁, hTM⟩ := terminal_mass hA1
  obtain ⟨b₂, hAll⟩ := allscales_of_bounds
  set b0 := max (max b₁ b₂) 1000000 with hb0def
  have hb01 : b₁ ≤ b0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb02 : b₂ ≤ b0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hb06 : 1000000 ≤ b0 := le_max_right _ _
  have hb0 : 100 ≤ b0 := le_trans (by norm_num) hb06
  -- `a₀`, `n₁` and the class `y mod 3^Q` (the terminal marked mass)
  obtain ⟨a₀, n₁, Q, y, ha₀, hmass⟩ := hTM b0 hb01
  -- the seed (Lemma 8.7)
  obtain ⟨M, hMo, hM16, hMy, hMa, hper⟩ := seed ha h3 Q (16 ^ b0) y
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMo.pos
  -- (8.1) with `A = 2`, and the coarse modulus `3^{m₀}`
  obtain ⟨C, hC⟩ := hA1 2 (by norm_num)
  set m0 : ℕ := ⌈64 * M * |C| / a₀⌉₊ + 1 with hm0def
  have hm0 : 1 ≤ m0 := Nat.le_add_left _ _
  have hm0r : 64 * M * |C| / a₀ ≤ m0 := by
    have := Nat.le_ceil (64 * M * |C| / a₀)
    rw [hm0def]; push_cast; linarith
  have hm0pos : (0 : ℝ) < m0 := by exact_mod_cast hm0
  have hfine : 128 / 3 * M * (2 / 3 * C * (m0 : ℝ) ^ (-(2 : ℝ))) ≤ a₀ / 2 := by
    have hrp : (m0 : ℝ) ^ (-(2 : ℝ)) = 1 / ((m0 : ℝ) * m0) := by
      rw [Real.rpow_neg hm0pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hrp]
    have h1 : C * (1 / ((m0 : ℝ) * m0)) ≤ |C| / m0 := by
      have hm1 : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0
      rw [div_eq_mul_one_div |C|]
      calc C * (1 / ((m0 : ℝ) * m0)) ≤ |C| * (1 / ((m0 : ℝ) * m0)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (1 / m0) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
            apply one_div_le_one_div_of_le hm0pos
            nlinarith
    have h2 : 64 * M * |C| ≤ m0 * a₀ := by rwa [div_le_iff₀ ha₀] at hm0r
    have h3 : |C| / m0 ≤ a₀ / (64 * M) := by
      rw [div_le_div_iff₀ hm0pos (by positivity)]; nlinarith
    calc 128 / 3 * M * (2 / 3 * C * (1 / ((m0 : ℝ) * m0)))
        = 256 / 9 * M * (C * (1 / ((m0 : ℝ) * m0))) := by ring
      _ ≤ 256 / 9 * M * (a₀ / (64 * M)) := by
          apply mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
      _ = 4 / 9 * a₀ := by field_simp; ring
      _ ≤ a₀ / 2 := by linarith
  -- large `X`: an admissible generation `n ≥ max n₁ m₀` (Lemma 8.8)
  have hev := hAll b0 hb02 M hMo hM16 (max n₁ m0)
  have hev' : ∀ᶠ Y : ℕ in atTop, ∃ n ≥ max n₁ m0, Admissible b0 M n ((Y : ℝ) / 32) :=
    (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 32)).eventually hev
  refine ⟨9 * a₀ / (16 * 3 ^ m0 * M) / 32, by positivity, ?_⟩
  filter_upwards [hev'] with Y hY
  obtain ⟨n, hn, hadm⟩ := hY
  have hmk : m0 ≤ kseq b0 n := le_trans (le_of_max_le_right hn) (le_kseq hb06 n)
  have hcount := count_at_scale hb0 hMo hM16 hper hMa hadm ha₀
    (hmass M hMo hM16 hMy n (le_of_max_le_left hn) _ hadm) (hC m0 (kseq b0 n) hm0 hmk) hfine
    (Y := Y) (by linarith)
  calc 9 * a₀ / (16 * 3 ^ m0 * M) / 32 * (Y : ℝ) = 9 * a₀ / (16 * 3 ^ m0 * M) * ((Y : ℝ) / 32) := by
        ring
    _ ≤ _ := hcount

/-- **Theorem 8.1 [`thm:positivity`]** from Tao's imports (through (8.1, `eq:A1`),
`offsetMixing_of_tao`). -/
theorem positivity_of_tao (hTM : TaoMajorant) (hTP : TaoPrefix) {a : ℕ} (ha : 0 < a)
    (h3 : ¬ 3 ∣ a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop, c * X ≤ ((window (Pred T a) X).card : ℝ) :=
  positivity_of_offsetMixing (offsetMixing_of_tao hTM hTP) ha h3

end Positivity
end CollatzCLT
