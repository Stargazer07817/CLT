import LeanClt.Transfer.Defs
import LeanClt.Renewal.Tails

/-!
# The geometric model: sums over words

* `mem_words`: `a ∈ words n s` iff `∑ a = s` and every letter is `≥ 1`.
* `sum_words_append`: a word of length `m + t` is a word of length `m` followed by a word of
  length `t` (the splitting used in the identity (5.12, `eq:identity`)).
* `sum_words_half`: `∑_{a ∈ words n s} 2^{-s} = P(S_n = s)`.
* `card_words_le`: `#words n s ≤ 2^s`.
-/

open Real Finset

namespace CollatzCLT

lemma mem_words {n s : ℕ} {a : Fin n → ℕ} :
    a ∈ words n s ↔ (∑ i, a i = s) ∧ ∀ i, 1 ≤ a i := by
  simp [words, Finset.Nat.mem_antidiagonalTuple]

/-- **Splitting a word.** -/
theorem sum_words_append {β : Type*} [AddCommMonoid β] (m t s : ℕ) (g : (Fin (m + t) → ℕ) → β) :
    ∑ a ∈ words (m + t) s, g a =
      ∑ s1 ∈ range (s + 1), ∑ u ∈ words m s1, ∑ v ∈ words t (s - s1), g (Fin.append u v) := by
  simp_rw [← Finset.sum_product']
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun a _ => ⟨∑ i, a (Fin.castAdd t i),
      (fun i => a (Fin.castAdd t i), fun i => a (Fin.natAdd m i))⟩)
    (fun x _ => Fin.append x.2.1 x.2.2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_words] at ha
    obtain ⟨hs, h1⟩ := ha
    rw [Fin.sum_univ_add] at hs
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_words]
    exact ⟨by omega, ⟨by simp, fun i => h1 _⟩, ⟨by omega, fun i => h1 _⟩⟩
  · rintro ⟨s1, u, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_words] at hx
    obtain ⟨hs1, ⟨hu, hu1⟩, ⟨hv, hv1⟩⟩ := hx
    rw [mem_words, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    refine ⟨by omega, fun i => ?_⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hu1 j
    · rw [Fin.append_right]; exact hv1 j
  · intro a _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨s1, u, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_words] at hx
    simp only [Fin.append_left, Fin.append_right, hx.2.1.1]
  · intro a _; exact congrArg g Fin.append_castAdd_natAdd.symm

lemma words_zero (s : ℕ) : words 0 s = if s = 0 then {Fin.elim0} else ∅ := by
  ext a
  rw [mem_words]
  split_ifs with h
  · simp [h, Subsingleton.elim a Fin.elim0]
  · simp [Ne.symm h]

lemma words_one (k : ℕ) : words 1 k = if 1 ≤ k then {fun _ => k} else ∅ := by
  ext a
  rw [mem_words]
  split_ifs with h
  · simp only [Finset.mem_singleton, Fin.sum_univ_one]
    constructor
    · rintro ⟨h1, -⟩; funext i; rw [Subsingleton.elim i 0, h1]
    · rintro rfl; exact ⟨rfl, fun _ => h⟩
  · simp only [Finset.notMem_empty, iff_false, not_and, Fin.sum_univ_one]
    intro h1 h2; have := h2 0; omega

/-- **`∑_{a ∈ words n s} 2^{-s} = P(S_n = s)`.** -/
theorem sum_words_half (n s : ℕ) : ∑ a ∈ words n s, (1 / 2 : ℝ) ^ s = lawS n s := by
  induction n generalizing s with
  | zero =>
    rw [words_zero]
    split_ifs with h
    · subst h; simp
    · simp [lawS, h]
  | succ n ih =>
    rw [sum_words_append n 1 s]
    simp_rw [words_one]
    -- only `s1 < s` contribute
    have : ∀ s1 ∈ range (s + 1), (∑ u ∈ words n s1,
        ∑ v ∈ (if 1 ≤ s - s1 then {fun _ => s - s1} else (∅ : Finset (Fin 1 → ℕ))),
          (1 / 2 : ℝ) ^ s) = if s1 < s then (1 / 2 : ℝ) ^ (s - s1) * lawS n s1 else 0 := by
      intro s1 hs1
      rw [mem_range] at hs1
      split_ifs with h1 h2 h2
      · rw [← ih s1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_singleton, ← pow_add]; congr 1; omega
      · omega
      · omega
      · simp
    rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
    have hfil : (range (s + 1)).filter (· < s) = range s := by
      ext k; simp only [mem_filter, mem_range]; omega
    rw [hfil]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [lawS]
    · obtain ⟨A, rfl⟩ : ∃ A, s = A + 1 := ⟨s - 1, by omega⟩
      simp only [lawS]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr 1
      all_goals (try congr 1)
      all_goals omega

lemma lawS_le_one (n s : ℕ) : lawS n s ≤ 1 := by
  have := (summable_lawS n).le_tsum s (fun j _ => lawS_nonneg _ _)
  rw [tsum_lawS] at this
  exact this

/-- `#words n s ≤ 2^s`. -/
lemma card_words_le (n s : ℕ) : ((words n s).card : ℝ) ≤ 2 ^ s := by
  have h := sum_words_half n s
  rw [Finset.sum_const, nsmul_eq_mul] at h
  have h1 := lawS_le_one n s
  have h2 : (0 : ℝ) < (1 / 2) ^ s := by positivity
  have : ((words n s).card : ℝ) * (1 / 2) ^ s ≤ 1 := by rw [h]; exact h1
  rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_one (by positivity)] at this
  exact this

end CollatzCLT
