import LeanClt.Transfer.Reverse

/-!
# §2.4: Tao's two imports used in §3, as explicit hypotheses

Both are stated in the language of finite words with the geometric weight `2^{-S}` (the law of
`Geom(2)^n`), as everywhere else in the development; neither is proved in Lean.

* `TaoMajorant` (**Imported Theorem 2.3**, `imp:majorant`; Tao, (7.4)–(7.5), Lemma 7.2,
  Prop. 7.3): for every `B > 0` there is `C_B` such that for all `n ≥ 1` and `3 ∤ ξ`,
  `E ∏_{j ≤ ⌊n/2⌋} |f_ξ(3^{2j-2} 2^{-B_j}, b_j)| ≤ C_B n^{-B}`, where `b_j = a_{2j-1} + a_{2j}`,
  `B_j = b_1 + ⋯ + b_j` and `f_ξ(x, b) = (b-1)⁻¹ ∑_{a=1}^{b-1} χ_ξ(x(2^a + 3))`,
  `χ_ξ(x) = e^{-2πi ξx/3^n}`.

* `TaoPrefix` (**Imported Theorem 2.4**, `imp:prefix`; Tao, (6.2)–(6.13), Lemma 6.2, Cor. 6.3),
  stated existentially: for every `L > 0` there are `C`, `K` and `n₀` such that for `n ≥ n₀`
  there is a finite family of prefix events `D_{p,l}` (sets of words of length `p` and total `l`)
  that are pairwise disjoint as events on `Geom(2)^ℕ`, cover all but `K n^{-L}` of the mass, number
  at most `K n²`, satisfy `p ≤ (log 3/(2 log 2)) n + K √(n log n)` and `l ≥ n log₂ 3 - C² log n`,
  and are **separated**: distinct words in one `D_{p,l}` have distinct offsets `X̃_p mod 3^n`.

  This is *weaker* than the paper's Imported Theorem 2.4: it omits the lower bound on `p` and the
  upper bound `l ≤ n log₂ 3 - 0.99 C² log n` (the latter, with the fluctuation window, is what Tao
  needs to *prove* separation; neither is used afterwards), and it lets the constant in the count
  `O(n²)` depend on `L`. The collision bound (2.7, `eq:collision`) is not assumed: it is derived
  from separation and the lower bound on `l` (`sum_prefLaw_sq_le`, `three_pow_mul_half_pow_le`).
-/

open Real Finset Complex

noncomputable section

namespace CollatzCLT

/-- The additive character `χ_ξ(x) = e^{-2πi ξx/3^n}` of `ℤ/3^nℤ`. -/
def chiZ {n : ℕ} (ξ x : ZMod (3 ^ n)) : ℂ :=
  cexp (((-(2 * π * ((ξ * x).val : ℝ) / 3 ^ n)) : ℝ) * I)

/-- Tao's pair average `f_ξ(x, b) = (b-1)⁻¹ ∑_{a=1}^{b-1} χ_ξ(x (2^a + 3))`. -/
def fTao {n : ℕ} (ξ x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b - 1 : ℕ) : ℂ)⁻¹ * ∑ a ∈ Icc 1 (b - 1), chiZ ξ (x * (2 ^ a + 3))

/-- The `(j+1)`-th pair sum `b_{j+1} = a_{2j+1} + a_{2j+2}` of a word (letters `0`-indexed). -/
def pairSum {n : ℕ} (a : Fin n → ℕ) (j : ℕ) : ℕ := ext a (2 * j) + ext a (2 * j + 1)

/-- The majorant integrand `∏_{j ≤ ⌊n/2⌋} |f_ξ(3^{2j-2} 2^{-B_j}, b_j)|` at a word
(with `B_j = S_{2j}`). -/
def majorantAt {n : ℕ} (ξ : ZMod (3 ^ n)) (a : Fin n → ℕ) : ℝ :=
  ∏ j ∈ range (n / 2),
    ‖fTao ξ ((3 : ZMod (3 ^ n)) ^ (2 * j) * half n ^ wsum (ext a) (2 * j + 2)) (pairSum a j)‖

/-- Tao's majorant `E ∏_{j ≤ ⌊n/2⌋} |f_ξ(3^{2j-2} 2^{-B_j}, b_j)|` under `Geom(2)^n`. -/
def taoMajorant (n : ℕ) (ξ : ZMod (3 ^ n)) : ℝ :=
  ∑' S : ℕ, ∑ a ∈ words n S, (1 / 2 : ℝ) ^ S * majorantAt ξ a

/-- **Imported Theorem 2.3 (Tao's majorant bound)**, as a hypothesis. -/
def TaoMajorant : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ 3 ∣ ξ.val →
    taoMajorant n ξ ≤ C * (n : ℝ) ^ (-B)

/-- The target-outward offset `X̃_p = ∑_{j=1}^p 3^{j-1} 2^{-S_j}` of a word of length `p`, reduced
modulo `3^n` (for any `n`; `Xmod` is the case `n = p`). -/
def XmodN (n : ℕ) {p : ℕ} (a : Fin p → ℕ) : ZMod (3 ^ n) :=
  ∑ j : Fin p, (3 : ZMod (3 ^ n)) ^ (j : ℕ) * half n ^ psum a j

/-- The length-`p` prefix of a word of length `p' ≥ p`. -/
def prefixOf {p p' : ℕ} (h : p ≤ p') (w : Fin p' → ℕ) : Fin p → ℕ := fun i => w (Fin.castLE h i)

/-- **Imported Theorem 2.4 (prefix decomposition and separation)**, as a hypothesis, in the
weakened existential form described in the module docstring. -/
def TaoPrefix : Prop :=
  ∀ L : ℝ, 0 < L → ∃ C K : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ (I : Finset (ℕ × ℕ)) (D : (p : ℕ) → ℕ → Finset (Fin p → ℕ)),
      -- at most `K n²` pieces
      (I.card : ℝ) ≤ K * (n : ℝ) ^ 2 ∧
      -- `D_{p,l}` consists of words of length `p` and total `l`
      (∀ pl ∈ I, D pl.1 pl.2 ⊆ words pl.1 pl.2) ∧
      -- the prefix length is at most `(log 3 / (2 log 2)) n + K √(n log n)`
      (∀ pl ∈ I, (pl.1 : ℝ) ≤ Real.log 3 / (2 * Real.log 2) * n + K * √(n * Real.log n)) ∧
      -- the prefix total is at least `n log₂ 3 - C² log n`
      (∀ pl ∈ I, (n : ℝ) * Real.logb 2 3 - C ^ 2 * Real.log n ≤ pl.2) ∧
      -- the events `{(a₁,…,a_p) ∈ D_{p,l}}` are pairwise disjoint
      (∀ pl ∈ I, ∀ pl' ∈ I, pl ≠ pl' → ∀ h : pl.1 ≤ pl'.1, ∀ w ∈ D pl'.1 pl'.2,
        prefixOf h w ∉ D pl.1 pl.2) ∧
      -- they cover all but `K n^{-L}` of the mass
      1 - K * (n : ℝ) ^ (-L) ≤ ∑ pl ∈ I, ((D pl.1 pl.2).card : ℝ) * (1 / 2 : ℝ) ^ pl.2 ∧
      -- separation: distinct words in one piece have distinct offsets mod `3^n`
      (∀ pl ∈ I, Set.InjOn (XmodN n) (↑(D pl.1 pl.2) : Set (Fin pl.1 → ℕ)))

end CollatzCLT
