import LeanClt.Positivity.Numerics

/-!
# §8.2 and §8.4: central and terminal blocks, and Lemma 8.4

**Blocks.** `FirstCross ℓ H K w`: the partial sums `A_j` of `w` stay strictly below the barrier `H`
at every depth `ℓ ≤ j < |w|`, reach it at depth `|w|`, and overshoot it by at most `K`.

* `IsCentral b K w`: `FirstCross ℓ_b H_b K w` and `|w| ∈ [b - ⌈b^{3/5}⌉, b + ⌈b^{3/5}⌉]` (§8.2);
* `IsTerminal b K u w`: `FirstCross ℓ_b (H_b + u - r_b) K w` and `|w| ≤ h_b` (§8.4).

The paper's parenthetical "(i.e. `A_{s-1} < H_b(s-1)`, `A_s ≥ H_b(s)`)" is weaker than "first
cross": the barrier can rise by 2 while the partial sums rise by 1, so a walk can touch the barrier
and fall below it again, and under the literal local test `V_{b,K}` is not prefix-free (point G1 of
checkpoint 06). `FirstCross` requires `A_j < H(j)` at **every** depth `ℓ_b ≤ j < |w|`, the reading
under which the paper's "finite and prefix-free" holds.

The finsets `central b K` and `terminal b K u` filter an explicit enumeration `wordsUpTo`. Both
families are prefix-free (`central_prefixFree`, `terminal_prefixFree`); `terminal` is exactly the
set of terminal blocks (`mem_terminal`), and `central` is exactly the set of central blocks once
`⌈b^{3/5}⌉ ≤ w_b` (`mem_central`, true for `b ≥ 32`).

**Geometric probabilities.** `prob n E = P(E)` for an event `E` on the first `n` letters of the
geometric word (i.i.d. `Geom(2)` letters). Tools: complements and finite unions (`prob_add_not`,
`prob_exists_le`, `sum_prob_le_one` for disjoint events), marginals (`prob_take`), the law of the
total (`prob_tot`), cylinders (`prob_prefix`), and **the first-crossing split** `prob_overshoot`
(memorylessness of `Geom(2)` at the crossing letter).

**Lemma 8.4 [`lem:C1`].** `block_rejection` and `block_rejection_prod`.
-/

open Finset Real Filter

noncomputable section

namespace CollatzCLT
namespace Positivity

/-! ## Central and terminal blocks -/

/-- `w` first crosses the barrier `Hs` (after depth `l`) at depth `|w|`, with overshoot `≤ K`. -/
def FirstCross (l : ℕ) (Hs : ℕ → ℤ) (K : ℕ) (w : Word) : Prop :=
  w.Pos ∧ l < w.length ∧ (∀ j ∈ Icc l (w.length - 1), (pre w j : ℤ) < Hs j) ∧
    Hs w.length ≤ pre w w.length ∧ (pre w w.length : ℤ) ≤ Hs w.length + K

/-- A central block at scale `b` with overshoot at most `K` (§8.2). -/
def IsCentral (b K : ℕ) (w : Word) : Prop :=
  FirstCross (lB b) (barrier b) K w ∧ w.length ≤ b + mB b ∧ b ≤ w.length + mB b

/-- A terminal block at scale `b` with shift `u` and overshoot at most `K` (§8.4). -/
def IsTerminal (b K u : ℕ) (w : Word) : Prop :=
  FirstCross (lB b) (fun s => barrier b s + u - rB b) K w ∧ w.length ≤ hB b

/-- All words with letters `≥ 1`, depth `≤ h` and total `≤ S`. -/
def wordsUpTo (h S : ℕ) : Finset Word :=
  (range (h + 1)).biUnion fun n => (range (S + 1)).biUnion fun s => (words n s).image List.ofFn

open Classical in
/-- The family `V_{b,K}` of central blocks (exactly the central blocks once `⌈b^{3/5}⌉ ≤ w_b`,
i.e. for `b ≥ 32`: `mem_central`). -/
def central (b K : ℕ) : Finset Word := (wordsUpTo (hB b) (4 * b + K)).filter (IsCentral b K)

open Classical in
/-- The family of terminal blocks with shift `u`. -/
def terminal (b K u : ℕ) : Finset Word :=
  (wordsUpTo (hB b) (4 * b + K + u)).filter (IsTerminal b K u)

/-- The scales `b_{j+1} = b_j + ⌊b_j/100⌋`, `b_0 = b0`. -/
def bseq (b0 : ℕ) : ℕ → ℕ
  | 0 => b0
  | j + 1 => bseq b0 j + bseq b0 j / 100

/-- `K_j = ⌊j/10⌋`. -/
def Kseq (j : ℕ) : ℕ := j / 10

/-- `k_n = ⌊b_n/4⌋`. -/
def kseq (b0 n : ℕ) : ℕ := bseq b0 n / 4

/-- `p_j`, the geometric probability of `V_{b_j,K_j}` (for `b_j ≥ 32`, see `central`). -/
def pj (b0 j : ℕ) : ℝ := pmass (central (bseq b0 j) (Kseq j))

/-! ## Membership and prefix-freeness -/

lemma ofFn_pos {n s : ℕ} {a : Fin n → ℕ} (ha : a ∈ words n s) : Word.Pos (List.ofFn a) := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (mem_words.mp ha).2 i

lemma mem_wordsUpTo {h S : ℕ} {w : Word} :
    w ∈ wordsUpTo h S ↔ w.Pos ∧ w.length ≤ h ∧ tot w ≤ S := by
  unfold wordsUpTo
  simp only [mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨n, hn, s, hs, a, ha, rfl⟩
    refine ⟨ofFn_pos ha, by rw [List.length_ofFn]; omega, ?_⟩
    rw [tot_ofFn, (mem_words.mp ha).1]; omega
  · rintro ⟨hp, hl, ht⟩
    exact ⟨w.length, by omega, tot w, by omega, w.get, (get_mem_words hp _).mpr rfl,
      List.ofFn_get w⟩

lemma pre_take {w : Word} {j k : ℕ} (h : j ≤ k) : pre (w.take k) j = pre w j := by
  unfold pre; rw [List.take_take, min_eq_left h]

lemma tot_le_of_firstCross {l : ℕ} {Hs : ℕ → ℤ} {K : ℕ} {w : Word} (h : FirstCross l Hs K w) :
    (tot w : ℤ) ≤ Hs w.length + K := by
  rw [← pre_length]; exact h.2.2.2.2

/-- Families of first-crossing words are prefix-free. -/
lemma prefixFree_of_firstCross {V : Finset Word} {l : ℕ} {Hs : ℕ → ℤ}
    (h : ∀ w ∈ V, ∃ K, FirstCross l Hs K w) : PrefixFree V := by
  intro v hv w hw hvw
  obtain ⟨K, -, hlv, -, hcv, -⟩ := h v hv
  obtain ⟨K', -, -, hbw, -, -⟩ := h w hw
  have hlen : v.length ≤ w.length := hvw.length_le
  by_contra hne
  have hlt : v.length < w.length := lt_of_le_of_ne hlen (fun he => hne (hvw.eq_of_length he))
  have hj := hbw v.length (Finset.mem_Icc.mpr ⟨hlv.le, by omega⟩)
  have e : w.take v.length = v := (List.prefix_iff_eq_take.mp hvw).symm
  have hpre : pre w v.length = pre v v.length := by
    unfold pre; rw [e, List.take_length]
  rw [hpre] at hj
  omega

lemma central_spec {b K : ℕ} {w : Word} (hw : w ∈ central b K) : IsCentral b K w := by
  classical
  unfold central at hw; exact (Finset.mem_filter.mp hw).2

lemma central_length_le {b K : ℕ} {w : Word} (hw : w ∈ central b K) : w.length ≤ hB b := by
  classical
  unfold central at hw; exact (mem_wordsUpTo.mp (Finset.mem_filter.mp hw).1).2.1

/-- `central b K` is exactly the set of central blocks once `⌈b^{3/5}⌉ ≤ w_b`. -/
lemma mem_central {b K : ℕ} (hb : mB b ≤ wB b) {w : Word} : w ∈ central b K ↔ IsCentral b K w := by
  classical
  unfold central
  rw [Finset.mem_filter, mem_wordsUpTo]
  refine ⟨fun h => h.2, fun h => ⟨⟨h.1.1, ?_, ?_⟩, h⟩⟩
  · unfold hB; have := h.2.1; omega
  · have ht := tot_le_of_firstCross h.1
    have hbar := barrier_le b w.length
    have h1 := h.2.1
    have hw : wB b ≤ b := by unfold wB; omega
    have h2 : w.length - b ≤ wB b := by omega
    omega

lemma central_prefixFree (b K : ℕ) : PrefixFree (central b K) :=
  prefixFree_of_firstCross fun _ hw => ⟨K, (central_spec hw).1⟩

lemma central_pos {b K : ℕ} {w : Word} (hw : w ∈ central b K) : w.Pos := (central_spec hw).1.1

/-- `terminal b K u` is exactly the set of terminal blocks with shift `u`. -/
lemma mem_terminal {b K u : ℕ} {w : Word} : w ∈ terminal b K u ↔ IsTerminal b K u w := by
  classical
  unfold terminal
  rw [Finset.mem_filter, mem_wordsUpTo]
  refine ⟨fun h => h.2, fun h => ⟨⟨h.1.1, h.2, ?_⟩, h⟩⟩
  have ht := tot_le_of_firstCross h.1
  have hbar := barrier_le b w.length
  have h1 := h.2
  unfold hB at h1
  have hw : wB b ≤ b := by unfold wB; omega
  have h2 : w.length - b ≤ wB b := by omega
  omega

lemma terminal_prefixFree (b K u : ℕ) : PrefixFree (terminal b K u) :=
  prefixFree_of_firstCross fun _ hw => ⟨K, (mem_terminal.mp hw).1⟩

/-! ## The witness `(1, 2, …, 2, 3)` -/

/-- The word `(1, 2, …, 2, 3)` of length `b` (target outwards). -/
def witness (b : ℕ) : Word := 1 :: (List.replicate (b - 2) 2 ++ [3])

lemma witness_length {b : ℕ} (hb : 2 ≤ b) : (witness b).length = b := by
  simp [witness]; omega

lemma witness_pos (b : ℕ) : (witness b).Pos := by
  intro a ha
  simp [witness, List.mem_replicate] at ha
  omega

lemma pre_witness {b i : ℕ} (hi : i ≤ b - 2) : pre (witness b) (i + 1) = 1 + 2 * i := by
  unfold witness
  rw [pre_cons_succ]
  unfold pre
  rw [List.take_append_of_le_length (by simp; omega), List.take_replicate, List.sum_replicate,
    min_eq_left hi, smul_eq_mul]
  ring

lemma tot_witness {b : ℕ} (hb : 2 ≤ b) : tot (witness b) = 2 * b := by
  simp [tot, witness, List.sum_replicate]; omega

lemma witness_central {b K : ℕ} (hb : 32 ≤ b) : witness b ∈ central b K := by
  rw [mem_central (mB_le_wB hb)]
  have hlen := witness_length (b := b) (by omega)
  have hw1 : 1 ≤ wB b := by unfold wB; omega
  have hwb := wB_lt (b := b) (by omega)
  have hpb : pre (witness b) b = 2 * b := by
    have := pre_length (witness b)
    rw [hlen] at this
    rw [this, tot_witness (by omega)]
  unfold IsCentral FirstCross
  rw [hlen, hpb]
  refine ⟨⟨witness_pos b, by unfold lB; omega, fun j hj => ?_, ?_, ?_⟩, by omega, by omega⟩
  · rw [Finset.mem_Icc] at hj
    have hl1 : 1 ≤ lB b := by unfold lB; omega
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [pre_witness (by omega)]
    have := two_mul_le_barrier (b := b) (s := i + 1) (by omega)
    push_cast at this ⊢
    omega
  · rw [barrier_of_le le_rfl]; simp
  · rw [barrier_of_le le_rfl]; simp

lemma central_pmass_pos {b : ℕ} (hb : 32 ≤ b) (K : ℕ) : 0 < pmass (central b K) :=
  lt_of_lt_of_le (gm_pos (witness b))
    (Finset.single_le_sum (fun w _ => (gm_pos w).le) (witness_central hb))

/-! ## Geometric probabilities of events on the first `n` letters -/

open Classical in
/-- `P(E)` for the first `n` letters of the geometric word:
`∑_S ∑_{a ∈ words n S, E(a)} 2^{-S}`. -/
def prob (n : ℕ) (E : Word → Prop) : ℝ :=
  ∑' S : ℕ, ∑ a ∈ words n S, if E (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0

open Classical in
lemma probTerm_nonneg (n S : ℕ) (E : Word → Prop) :
    0 ≤ ∑ a ∈ words n S, if E (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0 :=
  Finset.sum_nonneg fun a _ => by split_ifs <;> positivity

open Classical in
lemma probTerm_le (n S : ℕ) (E : Word → Prop) :
    (∑ a ∈ words n S, if E (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0) ≤ lawS n S := by
  rw [← sum_words_half]
  exact Finset.sum_le_sum fun a _ => by split_ifs; exacts [le_rfl, by positivity]

open Classical in
lemma summable_probTerm (n : ℕ) (E : Word → Prop) :
    Summable (fun S => ∑ a ∈ words n S, if E (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0) :=
  Summable.of_nonneg_of_le (fun S => probTerm_nonneg n S E) (fun S => probTerm_le n S E)
    (summable_lawS n)

lemma prob_nonneg (n : ℕ) (E : Word → Prop) : 0 ≤ prob n E :=
  tsum_nonneg fun S => probTerm_nonneg n S E

lemma prob_le_one (n : ℕ) (E : Word → Prop) : prob n E ≤ 1 := by
  unfold prob
  exact (Summable.tsum_le_tsum (fun S => probTerm_le n S E) (summable_probTerm n E)
    (summable_lawS n)).trans_eq (tsum_lawS n)

/-- Events that agree on words of length `n` with letters `≥ 1` have the same probability. -/
lemma prob_congr {n : ℕ} {E F : Word → Prop}
    (h : ∀ w : Word, w.length = n → w.Pos → (E w ↔ F w)) : prob n E = prob n F := by
  unfold prob
  refine tsum_congr fun S => Finset.sum_congr rfl fun a ha => ?_
  have h' := h (List.ofFn a) List.length_ofFn (ofFn_pos ha)
  by_cases hE : E (List.ofFn a)
  · rw [if_pos hE, if_pos (h'.mp hE)]
  · rw [if_neg hE, if_neg (fun hF => hE (h'.mpr hF))]

lemma prob_mono {n : ℕ} {E F : Word → Prop}
    (h : ∀ w : Word, w.length = n → w.Pos → E w → F w) : prob n E ≤ prob n F := by
  unfold prob
  refine Summable.tsum_le_tsum (fun S => Finset.sum_le_sum fun a ha => ?_)
    (summable_probTerm n E) (summable_probTerm n F)
  have h' := h (List.ofFn a) List.length_ofFn (ofFn_pos ha)
  by_cases hE : E (List.ofFn a)
  · rw [if_pos hE, if_pos (h' hE)]
  · rw [if_neg hE]; split_ifs <;> positivity

lemma prob_add_not (n : ℕ) (E : Word → Prop) : prob n E + prob n (fun w => ¬ E w) = 1 := by
  unfold prob
  rw [← Summable.tsum_add (summable_probTerm n E) (summable_probTerm n (fun w => ¬ E w))]
  refine (tsum_congr fun S => ?_).trans (tsum_lawS n)
  rw [← Finset.sum_add_distrib, ← sum_words_half]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hE : E (List.ofFn a)
  · rw [if_pos hE, if_neg (show ¬ ¬ E (List.ofFn a) from not_not.mpr hE), add_zero]
  · rw [if_neg hE, if_pos (show ¬ E (List.ofFn a) from hE), zero_add]

lemma prob_or_le (n : ℕ) (E F : Word → Prop) :
    prob n (fun w => E w ∨ F w) ≤ prob n E + prob n F := by
  unfold prob
  rw [← Summable.tsum_add (summable_probTerm n E) (summable_probTerm n F)]
  refine Summable.tsum_le_tsum (fun S => ?_) (summable_probTerm n (fun w => E w ∨ F w))
    ((summable_probTerm n E).add (summable_probTerm n F))
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hx : (0 : ℝ) ≤ (1 / 2) ^ S := by positivity
  split_ifs <;> first | linarith | (exfalso; tauto)

/-- The union bound over a finite family of events. -/
lemma prob_exists_le {ι : Type*} (n : ℕ) (I : Finset ι) (E : ι → Word → Prop) :
    prob n (fun w => ∃ i ∈ I, E i w) ≤ ∑ i ∈ I, prob n (E i) := by
  classical
  unfold prob
  rw [← Summable.tsum_finsetSum (fun i _ => summable_probTerm n (E i))]
  refine Summable.tsum_le_tsum (fun S => ?_) (summable_probTerm n (fun w => ∃ i ∈ I, E i w))
    (summable_sum fun i _ => summable_probTerm n (E i))
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  have hnn : ∀ i ∈ I, (0 : ℝ) ≤ if E i (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0 :=
    fun i _ => by split_ifs <;> positivity
  split_ifs with h
  · obtain ⟨i, hi, hEi⟩ := h
    refine le_trans ?_ (Finset.single_le_sum hnn hi)
    rw [if_pos hEi]
  · exact Finset.sum_nonneg hnn

/-- Pairwise disjoint events have total probability at most one. -/
lemma sum_prob_le_one {ι : Type*} {n : ℕ} (I : Finset ι) (E : ι → Word → Prop)
    (h : ∀ w : Word, w.length = n → w.Pos → ∀ i ∈ I, ∀ j ∈ I, E i w → E j w → i = j) :
    ∑ i ∈ I, prob n (E i) ≤ 1 := by
  classical
  unfold prob
  rw [← Summable.tsum_finsetSum (fun i _ => summable_probTerm n (E i))]
  refine (Summable.tsum_le_tsum (fun S => ?_) (summable_sum fun i _ => summable_probTerm n (E i))
    (summable_lawS n)).trans_eq (tsum_lawS n)
  rw [Finset.sum_comm, ← sum_words_half]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (I.filter (fun i => E i (List.ofFn a))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter] at hi hj
    exact h (List.ofFn a) List.length_ofFn (ofFn_pos ha) i hi.1 j hj.1 hi.2 hj.2
  calc ((I.filter (fun i => E i (List.ofFn a))).card : ℝ) * (1 / 2) ^ S ≤ 1 * (1 / 2) ^ S := by
        gcongr; exact_mod_cast hcard
    _ = (1 / 2) ^ S := one_mul _

/-- **Marginals:** an event on the first `k ≤ n` letters has the same probability at length `n`. -/
theorem prob_take {k n : ℕ} (hk : k ≤ n) (E : Word → Prop) :
    prob n (fun w => E (w.take k)) = prob k E := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, n = k + t := ⟨n - k, by omega⟩
  unfold prob
  have key : ∀ S, (∑ a ∈ words (k + t) S,
      if (fun w => E (w.take k)) (List.ofFn a) then (1 / 2 : ℝ) ^ S else 0) =
      ∑ s1 ∈ range (S + 1), (∑ u ∈ words k s1, if E (List.ofFn u) then (1 / 2 : ℝ) ^ s1 else 0) *
        lawS t (S - s1) := by
    intro S
    rw [sum_words_append k t S]
    refine Finset.sum_congr rfl fun s1 hs1 => ?_
    rw [Finset.mem_range] at hs1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← sum_words_half, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hS : (1 / 2 : ℝ) ^ S = (1 / 2) ^ s1 * (1 / 2) ^ (S - s1) := by
      rw [← pow_add]; congr 1; omega
    have hc : (fun w : Word => E (w.take k)) (List.ofFn (Fin.append u v)) ↔ E (List.ofFn u) := by
      dsimp only; rw [List.ofFn_fin_append, List.take_left' List.length_ofFn]
    by_cases hE : E (List.ofFn u)
    · rw [if_pos (hc.mpr hE), if_pos hE, hS]
    · rw [if_neg (fun h => hE (hc.mp h)), if_neg hE, zero_mul]
  rw [tsum_congr key]
  exact (conv_lawS (summable_probTerm k E) t).2

/-- The probability of an event on the total of the first `s` letters. -/
lemma prob_tot (s : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    prob s (fun w => P (tot w)) = ∑' A, if P A then lawS s A else 0 := by
  unfold prob
  refine tsum_congr fun A => ?_
  by_cases hP : P A
  · rw [if_pos hP, ← sum_words_half]
    refine Finset.sum_congr rfl fun a ha => ?_
    have : P (tot (List.ofFn a)) := by rwa [tot_ofFn, (mem_words.mp ha).1]
    rw [if_pos this]
  · rw [if_neg hP]
    refine Finset.sum_eq_zero fun a ha => ?_
    have : ¬ P (tot (List.ofFn a)) := by rwa [tot_ofFn, (mem_words.mp ha).1]
    rw [if_neg this]

/-- The probability of a single word is its geometric probability. -/
lemma prob_eq_word {w : Word} (hw : w.Pos) : prob w.length (fun x => x = w) = gm w := by
  classical
  unfold prob
  rw [show gm w = ∑' S : ℕ, if S = tot w then (1 / 2 : ℝ) ^ S else 0 by rw [tsum_ite_eq]; rfl]
  refine tsum_congr fun S => ?_
  trans ∑ a ∈ words w.length S, if a = w.get then (1 / 2 : ℝ) ^ S else 0
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hiff : List.ofFn a = w ↔ a = w.get := by
      constructor
      · intro h; apply List.ofFn_inj.mp; rw [h, List.ofFn_get]
      · rintro rfl; exact List.ofFn_get w
    by_cases h : a = w.get
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  · rw [Finset.sum_ite_eq']
    by_cases hS : S = tot w
    · rw [if_pos ((get_mem_words hw S).mpr hS), if_pos hS]
    · rw [if_neg (fun h => hS ((get_mem_words hw S).mp h)), if_neg hS]

/-- **Cylinders:** the event "`w` is a prefix" has probability `2^{-A(w)}`. -/
lemma prob_prefix {w : Word} (hw : w.Pos) {n : ℕ} (hn : w.length ≤ n) :
    prob n (fun x => w <+: x) = gm w := by
  rw [prob_congr (F := fun x => (fun y => y = w) (x.take w.length)) (fun x _ _ => by
    dsimp only; rw [List.prefix_iff_eq_take]; exact eq_comm)]
  rw [prob_take hn (fun y => y = w), prob_eq_word hw]

/-! ## The first-crossing split -/

lemma ofFn_append_one {k : ℕ} (u : Fin k → ℕ) (v : Fin 1 → ℕ) :
    List.ofFn (Fin.append u v) = List.ofFn u ++ [v 0] := by
  rw [List.ofFn_fin_append]; simp

open Classical in
/-- Splitting off the last letter of a word of length `k + 1`. -/
lemma probTerm_last (k S : ℕ) (P : Word → ℕ → Prop) :
    (∑ a ∈ words (k + 1) S,
        if (fun w : Word => P (w.take k) (w.getD k 0)) (List.ofFn a) then (1 / 2 : ℝ) ^ S
        else 0) =
      ∑ s1 ∈ range S, ∑ u ∈ words k s1, if P (List.ofFn u) (S - s1) then (1 / 2 : ℝ) ^ S
        else 0 := by
  rw [sum_words_append k 1 S, Finset.sum_range_succ, Nat.sub_self, words_one 0,
    if_neg (show ¬ (1 ≤ 0) by omega)]
  simp only [Finset.sum_empty, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun s1 hs1 => Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mem_range] at hs1
  rw [words_one, if_pos (show 1 ≤ S - s1 by omega), Finset.sum_singleton]
  have hc : (fun w : Word => P (w.take k) (w.getD k 0))
      (List.ofFn (Fin.append u fun _ : Fin 1 => S - s1)) ↔ P (List.ofFn u) (S - s1) := by
    dsimp only
    rw [ofFn_append_one, List.take_left' List.length_ofFn,
      List.getD_append_right (List.ofFn u) [S - s1] 0 k (by simp)]
    simp
  by_cases h : P (List.ofFn u) (S - s1)
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

/-- `∑_S f(S) = c ∑_S g(S)` when `f` is `c g` shifted by `A`. -/
lemma tsum_eq_mul_of_shift {f g : ℕ → ℝ} (A : ℕ) (c : ℝ) (hg : Summable g)
    (h : ∀ S, f S = if A ≤ S then c * g (S - A) else 0) : ∑' S, f S = c * ∑' S, g S := by
  rw [tsum_congr h, tsum_shift A (hg.mul_left c), tsum_mul_left]

lemma sum_range_add_eq_mul {F G : ℕ → ℝ} (S0 N : ℕ) (c : ℝ) (h1 : ∀ s1 < S0, F s1 = c * G s1)
    (h2 : ∀ x < N, F (S0 + x) = 0) :
    ∑ s1 ∈ range (S0 + N), F s1 = c * ∑ s1 ∈ range S0, G s1 := by
  rw [Finset.sum_range_add, Finset.sum_eq_zero (fun x hx => h2 x (Finset.mem_range.mp hx)),
    add_zero, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s1 hs => h1 s1 (Finset.mem_range.mp hs)

open Classical in
/-- **The first-crossing split** (memorylessness of `Geom(2)` at the crossing letter). For an
event `C` on the first `k` letters on which the gap `g` to the barrier at depth `k + 1` is
positive, overshooting the barrier by more than `K` at depth `k + 1` has probability `2^{-K-1}`
times that of crossing it there. -/
theorem prob_overshoot (k K : ℕ) (C : Word → Prop) (g : Word → ℤ)
    (hg : ∀ u : Word, u.length = k → u.Pos → C u → 1 ≤ g u) :
    prob (k + 1) (fun w => C (w.take k) ∧ g (w.take k) + K < (w.getD k 0 : ℤ)) =
      (1 / 2) ^ (K + 1) *
        prob (k + 1) (fun w => C (w.take k) ∧ g (w.take k) ≤ (w.getD k 0 : ℤ)) := by
  unfold prob
  refine tsum_eq_mul_of_shift (K + 1) _
    (summable_probTerm (k + 1) (fun w => C (w.take k) ∧ g (w.take k) ≤ (w.getD k 0 : ℤ)))
    fun S => ?_
  rw [probTerm_last k S (fun u c => C u ∧ g u + K < (c : ℤ))]
  by_cases hS : K + 1 ≤ S
  · obtain ⟨S0, rfl⟩ : ∃ S0, S = S0 + (K + 1) := ⟨S - (K + 1), by omega⟩
    rw [if_pos hS, Nat.add_sub_cancel, probTerm_last k S0 (fun u c => C u ∧ g u ≤ (c : ℤ))]
    refine sum_range_add_eq_mul S0 (K + 1) _ (fun s1 hs1 => ?_) (fun x hx => ?_)
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hC : C (List.ofFn u) ∧ g (List.ofFn u) ≤ ((S0 - s1 : ℕ) : ℤ)
      · rw [if_pos (show C (List.ofFn u) ∧ g (List.ofFn u) + K < ((S0 + (K + 1) - s1 : ℕ) : ℤ)
          from ⟨hC.1, by omega⟩), if_pos hC, pow_add]
        ring
      · rw [if_neg (show ¬ (C (List.ofFn u) ∧ g (List.ofFn u) + K <
            ((S0 + (K + 1) - s1 : ℕ) : ℤ)) from fun h => hC ⟨h.1, by omega⟩), if_neg hC, mul_zero]
    · refine Finset.sum_eq_zero fun u hu => if_neg ?_
      rintro ⟨hC, hlt⟩
      have := hg (List.ofFn u) List.length_ofFn (ofFn_pos hu) hC
      omega
  · rw [if_neg hS]
    refine Finset.sum_eq_zero fun s1 hs1 => Finset.sum_eq_zero fun u hu => if_neg ?_
    rintro ⟨hC, hlt⟩
    have := hg (List.ofFn u) List.length_ofFn (ofFn_pos hu) hC
    rw [Finset.mem_range] at hs1
    omega

/-! ## Lemma 8.4: the events -/

/-- Below the barrier `H_b` at every depth `ℓ_b ≤ j ≤ k` (an event on the first `k` letters). -/
def Below (b k : ℕ) (u : Word) : Prop := lB b ≤ k ∧ ∀ j ∈ Icc (lB b) k, (pre u j : ℤ) < barrier b j

/-- The gap `H_b(k+1) - A_k` to the barrier at depth `k + 1`. -/
def gap (b k : ℕ) (u : Word) : ℤ := barrier b (k + 1) - tot u

/-- First crossing of `H_b` at depth `k + 1` (an event on the first `k + 1` letters). -/
def CrossAt (b k : ℕ) (w : Word) : Prop :=
  Below b k (w.take k) ∧ gap b k (w.take k) ≤ (w.getD k 0 : ℤ)

/-- First crossing of `H_b` at depth `k + 1` with overshoot `> K`. -/
def OverAt (b K k : ℕ) (w : Word) : Prop :=
  Below b k (w.take k) ∧ gap b k (w.take k) + K < (w.getD k 0 : ℤ)

/-- A deviation `|A_s - 2s| ≥ ⌈b^{3/5}⌉/3` at depth `s`. -/
def Dev (b s : ℕ) (x : Word) : Prop := (mB b : ℝ) / 3 ≤ |((tot (x.take s) : ℕ) : ℝ) - 2 * s|

lemma one_le_gap {b k : ℕ} {u : Word} (hu : u.length = k) (h : Below b k u) : 1 ≤ gap b k u := by
  unfold gap
  have h1 := h.2 k (Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩)
  have h2 := barrier_mono b (show k ≤ k + 1 by omega)
  have h3 : pre u k = tot u := by rw [← hu, pre_length]
  rw [h3] at h1
  omega

/-- The first-crossing split for the barrier `H_b`. -/
lemma prob_overAt (b K k : ℕ) :
    prob (k + 1) (OverAt b K k) = (1 / 2) ^ (K + 1) * prob (k + 1) (CrossAt b k) :=
  prob_overshoot k K (Below b k) (gap b k) (fun _ hu _ h => one_le_gap hu h)

lemma take_take_succ (x : Word) (k : ℕ) : (x.take (k + 1)).take k = x.take k := by
  rw [List.take_take, min_eq_left (Nat.le_succ k)]

lemma getD_take_succ {x : Word} {k : ℕ} (hk : k < x.length) :
    (x.take (k + 1)).getD k 0 = x.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_take]; omega), List.getElem_take,
    List.getD_eq_getElem _ _ hk]

lemma pre_succ {x : Word} {k : ℕ} (hk : k < x.length) :
    pre x (k + 1) = tot (x.take k) + x.getD k 0 := by
  unfold pre tot; rw [List.sum_take_succ x k hk, List.getD_eq_getElem _ _ hk]

lemma crossAt_take_iff {b k : ℕ} {x : Word} (hk : k < x.length) :
    CrossAt b k (x.take (k + 1)) ↔ Below b k (x.take k) ∧ barrier b (k + 1) ≤ pre x (k + 1) := by
  unfold CrossAt gap
  rw [take_take_succ, getD_take_succ hk, pre_succ hk]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma overAt_take_iff {b K k : ℕ} {x : Word} (hk : k < x.length) :
    OverAt b K k (x.take (k + 1)) ↔
      Below b k (x.take k) ∧ barrier b (k + 1) + K < pre x (k + 1) := by
  unfold OverAt gap
  rw [take_take_succ, getD_take_succ hk, pre_succ hk]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma below_take {b k : ℕ} {x : Word} :
    Below b k (x.take k) ↔ lB b ≤ k ∧ ∀ j ∈ Icc (lB b) k, (pre x j : ℤ) < barrier b j := by
  unfold Below
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [← pre_take (Finset.mem_Icc.mp hj).2]; exact h2 j hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by rw [pre_take (Finset.mem_Icc.mp hj).2]; exact h2 j hj⟩

/-- A word first crosses the barrier at one depth only. -/
lemma crossAt_disjoint {b : ℕ} {x : Word} {k k' : ℕ} (hk : k < x.length) (hk' : k' < x.length)
    (h : CrossAt b k (x.take (k + 1))) (h' : CrossAt b k' (x.take (k' + 1))) : k = k' := by
  rw [crossAt_take_iff hk, below_take] at h
  rw [crossAt_take_iff hk', below_take] at h'
  obtain ⟨⟨hl, hb⟩, hc⟩ := h
  obtain ⟨⟨hl', hb'⟩, hc'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hb' (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    omega
  · have := hb (k' + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    omega

/-! ## Lemma 8.4: the two rejection mechanisms -/

/-- **Overshoot.** Summed over the depths, overshooting the barrier by more than `K` at the first
crossing has probability at most `2^{-K-1}`. -/
lemma prob_overshoot_le (b K n : ℕ) :
    prob n (fun x => ∃ k ∈ range n, OverAt b K k (x.take (k + 1))) ≤ (1 / 2) ^ (K + 1) := by
  refine (prob_exists_le n (range n) (fun k x => OverAt b K k (x.take (k + 1)))).trans ?_
  have e : ∀ k ∈ range n, prob n (fun x => OverAt b K k (x.take (k + 1))) =
      (1 / 2) ^ (K + 1) * prob n (fun x => CrossAt b k (x.take (k + 1))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [prob_take (by omega) (OverAt b K k), prob_overAt, prob_take (by omega) (CrossAt b k)]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have hd := sum_prob_le_one (n := n) (range n) (fun k x => CrossAt b k (x.take (k + 1)))
    (fun x hx _ k hk k' hk' h h' => crossAt_disjoint (by rw [Finset.mem_range] at hk; omega)
      (by rw [Finset.mem_range] at hk'; omega) h h')
  calc (1 / 2 : ℝ) ^ (K + 1) * ∑ k ∈ range n, prob n (fun x => CrossAt b k (x.take (k + 1)))
      ≤ (1 / 2) ^ (K + 1) * 1 := by gcongr
    _ = (1 / 2) ^ (K + 1) := mul_one _

/-- **Deviation at one depth** (Lemma 2.2(i), `lawS_chernoff`). -/
lemma prob_dev_le {b s : ℕ} (hb : 32 ≤ b) (hs1 : 1 ≤ s) (hs : s ≤ hB b) :
    prob (hB b) (Dev b s) ≤ 2 * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) := by
  have e1 : prob (hB b) (Dev b s) =
      prob s (fun w => (mB b : ℝ) / 3 ≤ |((tot w : ℕ) : ℝ) - 2 * s|) :=
    prob_take hs (fun w => (mB b : ℝ) / 3 ≤ |((tot w : ℕ) : ℝ) - 2 * s|)
  rw [e1, prob_tot s (fun A => (mB b : ℝ) / 3 ≤ |(A : ℝ) - 2 * s|)]
  refine (lawS_chernoff hs1 (x := (mB b : ℝ) / 3) (by positivity)).trans ?_
  have hbpos : (0 : ℝ) < b := by have : (32 : ℝ) ≤ b := by exact_mod_cast hb
                                 linarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hs2 : (s : ℝ) ≤ 2 * b := by
    have := hs.trans (hB_le b); exact_mod_cast this
  have hmb : (mB b : ℝ) ≤ b := by exact_mod_cast mB_le_self hb
  have hm0 : (0 : ℝ) ≤ mB b := Nat.cast_nonneg _
  gcongr
  rw [neg_div, neg_le_neg_iff]
  apply le_min
  · rw [show ((mB b : ℝ) / 3) ^ 2 / (12 * s) = (mB b : ℝ) ^ 2 / (108 * s) by ring]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- **Deviation at some depth**: the union bound over the `h_b ≤ 2b` depths. -/
lemma prob_dev_exists_le {b : ℕ} (hb : 32 ≤ b) :
    prob (hB b) (fun x => ∃ s ∈ Icc 1 (hB b), Dev b s x) ≤
      (4 * b + 4) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) := by
  refine (prob_exists_le (hB b) (Icc 1 (hB b)) (fun s x => Dev b s x)).trans ?_
  calc ∑ s ∈ Icc 1 (hB b), prob (hB b) (fun x => Dev b s x)
      ≤ ∑ s ∈ Icc 1 (hB b), 2 * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) :=
        Finset.sum_le_sum fun s hs =>
          prob_dev_le hb (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    _ = (hB b : ℝ) * (2 * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ (4 * b + 4) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) := by
        have h' : (hB b : ℝ) ≤ 2 * b := by exact_mod_cast hB_le b
        have he := Real.exp_pos (-((mB b : ℝ) ^ 2) / (576 * b))
        nlinarith

/-- **The deterministic core of Lemma 8.4.** A word of length `h_b` with no central prefix either
deviates by `⌈b^{3/5}⌉/3` from its mean `2s` at some depth `s ≤ h_b`, or first crosses the barrier
with overshoot `> K`. -/
lemma central_or_bad {b K : ℕ} (hb : 64 ≤ b) {x : Word} (hx : x.length = hB b) (hpos : x.Pos)
    (hnot : ¬ ∃ w ∈ central b K, w <+: x) :
    (∃ s ∈ Icc 1 (hB b), Dev b s x) ∨ ∃ k ∈ range (hB b), OverAt b K k (x.take (k + 1)) := by
  classical
  by_cases hd : ∃ s ∈ Icc 1 (hB b), Dev b s x
  · exact Or.inl hd
  right
  push_neg at hd
  have hm12 := twelve_le_mB (b := b) (by omega)
  have hmw := mB_le_wB (b := b) (by omega)
  have hwb := wB_lt (b := b) (by omega)
  -- no deviation, in `ℤ`
  have hdev : ∀ s, 1 ≤ s → s ≤ hB b →
      3 * (pre x s : ℤ) < 6 * s + mB b ∧ 6 * (s : ℤ) < 3 * pre x s + mB b := by
    intro s h1 h2
    have h := hd s (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    unfold Dev at h
    push_neg at h
    rw [abs_lt] at h
    have e : ((tot (x.take s) : ℕ) : ℝ) = ((pre x s : ℕ) : ℝ) := rfl
    rw [e] at h
    obtain ⟨h3, h4⟩ := h
    constructor
    · have : ((3 * (pre x s : ℤ) : ℤ) : ℝ) < ((6 * s + mB b : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((6 * (s : ℤ) : ℤ) : ℝ) < ((3 * pre x s + mB b : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  -- the walk has crossed by depth `b + m`
  have hbm : b + mB b ≤ hB b := by unfold hB; omega
  have hc : barrier b (b + mB b) ≤ pre x (b + mB b) := by
    rw [barrier_of_ge (by omega), Nat.add_sub_cancel_left]
    have h5 := five_mul_Bc_le (mB b)
    have h6 := (hdev (b + mB b) (by omega) hbm).2
    push_cast at h6
    omega
  have hex : ∃ s, lB b < s ∧ barrier b s ≤ pre x s := ⟨b + mB b, by unfold lB; omega, hc⟩
  obtain ⟨hls, hcs⟩ : lB b < Nat.find hex ∧ barrier b (Nat.find hex) ≤ pre x (Nat.find hex) :=
    Nat.find_spec hex
  have hsle : Nat.find hex ≤ b + mB b := Nat.find_min' hex ⟨by unfold lB; omega, hc⟩
  have hsmin : ∀ j, lB b < j → j < Nat.find hex → (pre x j : ℤ) < barrier b j := by
    intro j hj1 hj2
    have := Nat.find_min hex hj2
    push_neg at this
    exact this hj1
  set s := Nat.find hex with hs_def
  -- the first crossing is not before `b - m`
  have hsge : b ≤ s + mB b := by
    by_contra hlt
    push_neg at hlt
    have hsb : s ≤ b := by omega
    have h8 := five_mul_Bc_le (b - s)
    have h9 := (hdev s (by omega) (by omega)).1
    rw [barrier_of_le hsb] at hcs
    omega
  -- below the barrier at `ℓ_b`
  have hl1 : 1 ≤ lB b := by unfold lB; omega
  have hlow : (pre x (lB b) : ℤ) < barrier b (lB b) := by
    have hlb : lB b ≤ b := by unfold lB; omega
    rw [barrier_of_le hlb, show b - lB b = wB b by unfold lB; omega]
    have h5 := five_mul_Bc_le (wB b)
    have h6 := (hdev (lB b) hl1 (by unfold hB; omega)).1
    have h7 : lB b + wB b = b := by unfold lB; omega
    omega
  have hbelow : ∀ j ∈ Icc (lB b) (s - 1), (pre x j : ℤ) < barrier b j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.eq_or_lt_of_le hj.1 with h | h
    · rw [← h]; exact hlow
    · exact hsmin j h (by omega)
  by_cases hK : (pre x s : ℤ) ≤ barrier b s + K
  · exfalso
    apply hnot
    refine ⟨x.take s, ?_, List.take_prefix s x⟩
    rw [mem_central hmw]
    have hlen : (x.take s).length = s := by rw [List.length_take]; omega
    unfold IsCentral FirstCross
    rw [hlen, pre_take le_rfl]
    refine ⟨⟨fun a ha => hpos a (List.mem_of_mem_take ha), hls, fun j hj => ?_, hcs, hK⟩,
      hsle, hsge⟩
    rw [pre_take ((Finset.mem_Icc.mp hj).2.trans (Nat.sub_le s 1))]
    exact hbelow j hj
  · refine ⟨s - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hs1 : s - 1 + 1 = s := by omega
    rw [overAt_take_iff (k := s - 1) (x := x) (by omega), below_take, hs1]
    exact ⟨⟨by omega, fun j hj => hbelow j hj⟩, by push_neg at hK; exact hK⟩

/-- The rejection bound of Lemma 8.4 at one scale `b ≥ 64`. -/
theorem one_sub_pmass_central_le {b : ℕ} (hb : 64 ≤ b) (K : ℕ) :
    1 - pmass (central b K) ≤
      (4 * b + 4) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) + (1 / 2) ^ (K + 1) := by
  have h1 : prob (hB b) (fun x => ∃ w ∈ central b K, w <+: x) ≤ pmass (central b K) := by
    refine (prob_exists_le (hB b) (central b K) (fun w x => w <+: x)).trans (le_of_eq ?_)
    unfold pmass
    exact Finset.sum_congr rfl fun w hw => prob_prefix (central_pos hw) (central_length_le hw)
  have h2 := prob_add_not (hB b) (fun x => ∃ w ∈ central b K, w <+: x)
  have h3 : prob (hB b) (fun x => ¬ ∃ w ∈ central b K, w <+: x) ≤
      prob (hB b) (fun x => (∃ s ∈ Icc 1 (hB b), Dev b s x) ∨
        ∃ k ∈ range (hB b), OverAt b K k (x.take (k + 1))) :=
    prob_mono fun x hx hp hnot => central_or_bad hb hx hp hnot
  have h4 := prob_or_le (hB b) (fun x => ∃ s ∈ Icc 1 (hB b), Dev b s x)
    (fun x => ∃ k ∈ range (hB b), OverAt b K k (x.take (k + 1)))
  have h5 := prob_dev_exists_le (b := b) (by omega)
  have h6 := prob_overshoot_le b K (hB b)
  linarith

/-- **Lemma 8.4 [`lem:C1`]**, at one scale: `V_{b,K}` is prefix-free, `p(V_{b,K}) > 0`, and
`1 - p(V_{b,K}) ≤ (4b + 4) exp(-⌈b^{3/5}⌉²/(576 b)) + 2^{-K-1}`, for all `b ≥ b₁`. -/
theorem block_rejection : ∃ b₁ : ℕ, ∀ b ≥ b₁, ∀ K : ℕ,
    PrefixFree (central b K) ∧ 0 < pmass (central b K) ∧
      1 - pmass (central b K) ≤
        (4 * b + 4) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) + (1 / 2) ^ (K + 1) :=
  ⟨64, fun b hb K => ⟨central_prefixFree b K, central_pmass_pos (by omega) K,
    one_sub_pmass_central_le hb K⟩⟩

/-! ## The scales `b_j` and the product of the `p_j` -/

lemma bseq_succ (b0 j : ℕ) : bseq b0 (j + 1) = bseq b0 j + bseq b0 j / 100 := rfl

lemma le_bseq (b0 j : ℕ) : b0 ≤ bseq b0 j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => rw [bseq_succ]; omega

lemma bseq_mono (b0 : ℕ) {i j : ℕ} (h : i ≤ j) : bseq b0 i ≤ bseq b0 j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [bseq_succ]; omega)

/-- `b_j ≥ b_0 (201/200)^j` once `b_0 ≥ 200`. -/
lemma bseq_lower {b0 : ℕ} (hb : 200 ≤ b0) (j : ℕ) : (b0 : ℝ) * (201 / 200) ^ j ≤ bseq b0 j := by
  induction j with
  | zero => simp [bseq]
  | succ j ih =>
    have h1 : 200 ≤ bseq b0 j := hb.trans (le_bseq b0 j)
    have h2 : 201 * bseq b0 j ≤ 200 * bseq b0 (j + 1) := by rw [bseq_succ]; omega
    have h2' : (201 : ℝ) * bseq b0 j ≤ 200 * bseq b0 (j + 1) := by exact_mod_cast h2
    rw [pow_succ]
    nlinarith

/-- `b_j ≤ b_0 (101/100)^j`. -/
lemma bseq_upper (b0 j : ℕ) : (bseq b0 j : ℝ) ≤ b0 * (101 / 100) ^ j := by
  induction j with
  | zero => simp [bseq]
  | succ j ih =>
    have h2 : 100 * bseq b0 (j + 1) ≤ 101 * bseq b0 j := by rw [bseq_succ]; omega
    have h2' : (100 : ℝ) * bseq b0 (j + 1) ≤ 101 * bseq b0 j := by exact_mod_cast h2
    rw [pow_succ]
    nlinarith

/-- `(4b + 4) exp(-⌈b^{3/5}⌉²/(576 b)) ≤ C/b`, from `e^y ≥ y^{10}/10!` and `⌈b^{3/5}⌉^5 ≥ b^3`. -/
lemma rejection_term_le {b : ℕ} (hb : 1 ≤ b) :
    (4 * b + 4 : ℝ) * Real.exp (-((mB b : ℝ) ^ 2) / (576 * b)) ≤
      8 * ((Nat.factorial 10 : ℝ) * 576 ^ 10) / b := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  set y : ℝ := (mB b : ℝ) ^ 2 / (576 * b) with hy
  have hy0 : 0 ≤ y := by positivity
  have hexp := Real.pow_div_factorial_le_exp y hy0 10
  have hm : (b : ℝ) ^ 12 ≤ (mB b : ℝ) ^ 20 := by
    have h := Nat.pow_le_pow_left (pow_three_le_mB_pow_five b) 4
    rw [← pow_mul, ← pow_mul] at h
    exact_mod_cast h
  have hy10 : (b : ℝ) ^ 2 / 576 ^ 10 ≤ y ^ 10 := by
    rw [hy, div_pow, mul_pow, ← pow_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (b : ℝ) ^ 2 * (576 ^ 10 * (b : ℝ) ^ 10) = 576 ^ 10 * (b : ℝ) ^ 12 := by ring
    rw [this, show (mB b : ℝ) ^ (2 * 10) = (mB b : ℝ) ^ 20 by norm_num]
    nlinarith
  have hF : (0 : ℝ) < Nat.factorial 10 := by exact_mod_cast Nat.factorial_pos 10
  have hlow : (b : ℝ) ^ 2 / (576 ^ 10 * Nat.factorial 10) ≤ Real.exp y := by
    calc (b : ℝ) ^ 2 / (576 ^ 10 * Nat.factorial 10)
        = ((b : ℝ) ^ 2 / 576 ^ 10) / Nat.factorial 10 := by rw [div_div]
      _ ≤ y ^ 10 / Nat.factorial 10 := by gcongr
      _ ≤ Real.exp y := hexp
  have hneg : -((mB b : ℝ) ^ 2) / (576 * b) = -y := by rw [hy, neg_div]
  rw [hneg, Real.exp_neg]
  have hpos2 : 0 < (b : ℝ) ^ 2 / (576 ^ 10 * Nat.factorial 10) := by positivity
  have hinv : (Real.exp y)⁻¹ ≤ (576 ^ 10 * Nat.factorial 10) / (b : ℝ) ^ 2 := by
    rw [← inv_div]; exact inv_anti₀ hpos2 hlow
  calc (4 * b + 4 : ℝ) * (Real.exp y)⁻¹
      ≤ (8 * b) * ((576 ^ 10 * Nat.factorial 10) / (b : ℝ) ^ 2) :=
        mul_le_mul (by linarith) hinv (by positivity) (by positivity)
    _ = 8 * ((Nat.factorial 10 : ℝ) * 576 ^ 10) / b := by field_simp

lemma half_pow_div_ten_le (j : ℕ) : (1 / 2 : ℝ) ^ (j / 10) ≤ (16 / 15) ^ 9 * (15 / 16) ^ j := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 10 ∧ j = 10 * q + r :=
    ⟨j / 10, j % 10, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 10).symm⟩
  rw [show (10 * q + r) / 10 = q by omega, pow_add, pow_mul]
  have h1 : (1 / 2 : ℝ) ^ q ≤ ((15 / 16 : ℝ) ^ 10) ^ q :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) q
  have h2 : (15 / 16 : ℝ) ^ 9 ≤ (15 / 16) ^ r :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : (16 / 15 : ℝ) ^ 9 * (15 / 16) ^ 9 = 1 := by rw [← mul_pow]; norm_num
  calc (1 / 2 : ℝ) ^ q ≤ ((15 / 16) ^ 10) ^ q := h1
    _ = ((16 / 15) ^ 9 * (15 / 16) ^ 9) * ((15 / 16) ^ 10) ^ q := by rw [h3, one_mul]
    _ ≤ ((16 / 15) ^ 9 * (15 / 16) ^ r) * ((15 / 16) ^ 10) ^ q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    _ = (16 / 15) ^ 9 * (((15 / 16) ^ 10) ^ q * (15 / 16) ^ r) := by ring

lemma half_pow_Kseq_le (j : ℕ) : (1 / 2 : ℝ) ^ (Kseq j + 1) ≤ (16 / 15) ^ 9 * (15 / 16) ^ j :=
  (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold Kseq; omega)).trans
    (half_pow_div_ten_le j)

lemma one_sub_sum_le_prod {p : ℕ → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (s : Finset ℕ) : 1 - ∑ j ∈ s, (1 - p j) ≤ ∏ j ∈ s, p j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : 0 ≤ ∏ j ∈ s, p j := Finset.prod_nonneg fun j _ => hp0 j
    have h2 : ∏ j ∈ s, p j ≤ 1 := Finset.prod_le_one₀ (fun j _ => hp0 j) (fun j _ => hp1 j)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hp1 a)) (sub_nonneg.mpr h2), hp0 a]

/-- Factors in `(0, 1]` with `∑ (1 - p_j) < ∞` have partial products bounded below. -/
lemma exists_pos_le_prod {p : ℕ → ℝ} (hp0 : ∀ j, 0 < p j) (hp1 : ∀ j, p j ≤ 1)
    (hs : Summable (fun j => 1 - p j)) : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ ∏ j ∈ range n, p j := by
  have ht := tendsto_sum_nat_add (fun j => 1 - p j)
  obtain ⟨J, hJ⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  have hP0 : 0 < ∏ j ∈ range J, p j := Finset.prod_pos fun j _ => hp0 j
  refine ⟨(∏ j ∈ range J, p j) / 2, by positivity, fun n => ?_⟩
  rcases le_total n J with hn | hn
  · have e := (Finset.prod_range_mul_prod_Ico p hn).symm
    have h1 : ∏ j ∈ Ico n J, p j ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => (hp0 j).le) (fun j _ => hp1 j)
    have h2 : 0 ≤ ∏ j ∈ range n, p j := Finset.prod_nonneg fun j _ => (hp0 j).le
    rw [e]
    nlinarith
  · have e := (Finset.prod_range_mul_prod_Ico p hn).symm
    have h1 := one_sub_sum_le_prod (fun j => (hp0 j).le) hp1 (Ico J n)
    have hs' : Summable (fun k => 1 - p (k + J)) := (summable_nat_add_iff J).mpr hs
    have h2 : ∑ j ∈ Ico J n, (1 - p j) ≤ ∑' k, (1 - p (k + J)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      calc ∑ k ∈ range (n - J), (1 - p (J + k)) = ∑ k ∈ range (n - J), (1 - p (k + J)) :=
            Finset.sum_congr rfl fun k _ => by rw [add_comm]
        _ ≤ ∑' k, (1 - p (k + J)) :=
            hs'.sum_le_tsum (range (n - J)) (fun k _ => sub_nonneg.mpr (hp1 _))
    rw [e]
    nlinarith

/-- **Lemma 8.4 [`lem:C1`]**, along the scales `b_j`: `∑_j (1 - p_j) < ∞`, and the partial
products of the `p_j` are bounded below by a positive constant (the paper's `p_∞ > 0`). -/
theorem block_rejection_prod : ∃ b₁ : ℕ, ∀ b0 ≥ b₁,
    Summable (fun j => 1 - pj b0 j) ∧ ∃ p : ℝ, 0 < p ∧ ∀ n, p ≤ ∏ j ∈ range n, pj b0 j := by
  refine ⟨200, fun b0 hb0 => ?_⟩
  have hbj : ∀ j, 200 ≤ bseq b0 j := fun j => hb0.trans (le_bseq b0 j)
  have hpos : ∀ j, 0 < pj b0 j := fun j => central_pmass_pos (by have := hbj j; omega) _
  have hle1 : ∀ j, pj b0 j ≤ 1 := fun j =>
    pmass_le_one (central_prefixFree _ _) (fun _ hw => central_pos hw)
  have hb0pos : (0 : ℝ) < b0 := by
    have : (200 : ℝ) ≤ b0 := by exact_mod_cast hb0
    linarith
  set C : ℝ := 8 * ((Nat.factorial 10 : ℝ) * 576 ^ 10) with hC
  have hC0 : 0 ≤ C := by positivity
  have hrej : ∀ j, 1 - pj b0 j ≤ C / b0 * (200 / 201) ^ j + (16 / 15) ^ 9 * (15 / 16) ^ j := by
    intro j
    have h1 := one_sub_pmass_central_le (b := bseq b0 j) (by have := hbj j; omega) (Kseq j)
    have h2 := rejection_term_le (b := bseq b0 j) (by have := hbj j; omega)
    have hl := bseq_lower hb0 j
    have h3 : C / bseq b0 j ≤ C / b0 * (200 / 201) ^ j := by
      calc C / bseq b0 j ≤ C / (b0 * (201 / 200) ^ j) :=
            div_le_div_of_nonneg_left hC0 (by positivity) hl
        _ = C / b0 * (200 / 201) ^ j := by
            rw [show (200 / 201 : ℝ) ^ j = ((201 / 200) ^ j)⁻¹ by rw [← inv_pow]; norm_num]
            field_simp
    have h4 := half_pow_Kseq_le j
    unfold pj
    linarith
  have hsum : Summable (fun j => 1 - pj b0 j) :=
    Summable.of_nonneg_of_le (fun j => sub_nonneg.mpr (hle1 j)) hrej
      (((summable_geometric_of_lt_one (by norm_num) (by norm_num : (200 / 201 : ℝ) < 1)).mul_left
        (C / b0)).add
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (15 / 16 : ℝ) < 1)).mul_left
          ((16 / 15) ^ 9)))
  exact ⟨hsum, exists_pos_le_prod hpos hle1 hsum⟩

/-- The `p_j` lie in `(0, 1]` once `b_0 ≥ 32`; with `block_rejection_prod` this makes the
partial products nonincreasing, so their positive lower bound is the paper's `p_∞ > 0`. -/
lemma pj_pos_le_one {b0 : ℕ} (hb0 : 32 ≤ b0) (j : ℕ) : 0 < pj b0 j ∧ pj b0 j ≤ 1 :=
  ⟨central_pmass_pos (hb0.trans (le_bseq b0 j)) _,
    pmass_le_one (central_prefixFree _ _) (fun _ hw => central_pos hw)⟩

end Positivity
end CollatzCLT
