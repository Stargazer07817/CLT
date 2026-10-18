import LeanClt.Defs
import LeanClt.Elementary.Flow

/-!
# Definitions for Theorem 1.3 and Corollaries 1.5–1.6

The objects of Theorem 1.3 [`thm:thresholds`], Theorems 6.7 [`thm:rayentry`] and 6.8
[`thm:movingray`], and Corollaries 1.5 [`cor:dichotomy`] and 1.6 [`cor:unconditional`], written
over the existing `T`, `Pred`, `hit`, `Merge` and `IsPeriodic`, which are reused unchanged.

Modelling notes.
* First entry times (`entry`, `tauK`, `rayIndex`) are `sInf`s, like `hit`: off the relevant basin the
  set is empty and Lean's convention `sInf ∅ = 0` applies. Every statement about them is restricted
  to the basin (`Reach`, `AK`, `mergeClass`, `Pred`).
* `fwdOrbit a` is the forward `T`-orbit of `a`: the ray `R = {a_j}` when `a` is nonrepeating, the
  cycle through `a` when `a` is periodic.
* The merging classes are the classes of `mergeSetoid` on `ℕ`. The quotient has one extra class,
  that of `0` (`T 0 = 0`, and no positive integer merges with `0`); its `classSet` is empty.
* A choice of reference orbits for Corollary 1.6 is a function `ref : ℕ → ℕ` (`RefChoice`), and
  `O_{C(n)}` is `fwdOrbit (ref n)`.
-/

open Real

noncomputable section

namespace CollatzCLT

/-- First entry time of the `T`-orbit of `n` into `S` (`sInf ∅ = 0` off the basin of `S`). -/
def entry (S : Set ℕ) (n : ℕ) : ℕ := sInf {k | T^[k] n ∈ S}

/-- Positive integers whose `T`-orbit meets `S` (the basin of `S`). -/
def Reach (S : Set ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, T^[k] n ∈ S}

/-- `A_K = {n ≥ 1 : T^k(n) ≤ K for some k ≥ 0}` (Theorem 1.3 [`thm:thresholds`]). -/
def AK (K : ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, T^[k] n ≤ K}

/-- `τ_K(n)`, the first entry time into `[1, K]` (only meaningful on `A_K`). -/
def tauK (K : ℕ) (n : ℕ) : ℕ := sInf {k | T^[k] n ≤ K}

/-- The forward `T`-orbit `{T^j(a) : j ≥ 0}`: the ray `R = {a_j}` when `a` is nonrepeating,
the cycle through `a` when `a` is periodic. -/
def fwdOrbit (a : ℕ) : Set ℕ := Set.range (fun j => T^[j] a)

/-- `a` starts a nonrepeating `T`-ray (§6.7): its iterates are pairwise distinct. -/
def NonRepeating (a : ℕ) : Prop := Function.Injective (fun j => T^[j] a)

/-- The entrance index `J_R(n)`: the index `j` of the first ray point `a_j` reached. -/
def rayIndex (a n : ℕ) : ℕ := sInf {j | T^[entry (fwdOrbit a) n] n = T^[j] a}

/-- The merging class of `n`, positive members only. -/
def mergeClass (n : ℕ) : Set ℕ := {m | 0 < m ∧ Merge m n}

/-- Merging as a setoid on `ℕ`; the merging classes are its quotient (plus the class `{0}`,
whose `classSet` is empty). -/
def mergeSetoid : Setoid ℕ := ⟨Merge, merge_equivalence⟩

/-- The positive members of a class of the quotient. -/
def classSet (C : Quotient mergeSetoid) : Set ℕ :=
  {m | 0 < m ∧ Quotient.mk mergeSetoid m = C}

/-- `E = ℕ_{>0} \ P_T(1)`, the set of Collatz counterexamples (Corollary 1.5 [`cor:dichotomy`]). -/
def Exc : Set ℕ := {n | 0 < n ∧ n ∉ Pred T 1}

/-- An admissible choice of reference orbits (Corollary 1.6 [`cor:unconditional`]): `ref n` is a
positive point of the class of `n`, depends only on the class, and is periodic whenever the class
contains a periodic point. `O_{C(n)}` is `fwdOrbit (ref n)`: the cycle of a cyclic class, a forward
orbit of the class otherwise. -/
def RefChoice (ref : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < ref n ∧ Merge (ref n) n) ∧
  (∀ m n, 0 < m → 0 < n → Merge m n → ref m = ref n) ∧
  (∀ n, 0 < n → (∃ p, 0 < p ∧ Merge p n ∧ IsPeriodic p) → IsPeriodic (ref n))

/-- `ε(n)`, the first entry time of `n` into the reference orbit of its class. -/
def eps (ref : ℕ → ℕ) (n : ℕ) : ℕ := entry (fwdOrbit (ref n)) n

/-! ## First entry times -/

lemma iterate_entry {S : Set ℕ} {n : ℕ} (h : ∃ k, T^[k] n ∈ S) : T^[entry S n] n ∈ S :=
  Nat.sInf_mem h

lemma entry_le {S : Set ℕ} {n k : ℕ} (h : T^[k] n ∈ S) : entry S n ≤ k :=
  Nat.sInf_le h

lemma not_mem_of_lt_entry {S : Set ℕ} {n k : ℕ} (hk : k < entry S n) : T^[k] n ∉ S :=
  fun h => absurd (entry_le h) (not_le.mpr hk)

/-- `A_K` is the basin of `{m ≤ K}`, and `τ_K` is the first entry time into it. -/
lemma AK_eq (K : ℕ) : AK K = Reach {m | m ≤ K} := rfl

lemma tauK_eq (K : ℕ) : tauK K = entry {m | m ≤ K} := rfl

/-- `P_T(b)` is the basin of `{b}`, and `τ_{T,b}` is the first entry time into it. -/
lemma pred_eq_reach (b : ℕ) : Pred T b = Reach {b} := rfl

lemma hit_eq_entry (b : ℕ) : hit T b = entry {b} := rfl

/-- **Shifting along a segment that avoids `S`** (the set form of `pred_shift`): if the first `k`
states of the orbit of `N` avoid `S` and `T^k(N) = M`, then `N` and `M` have the same basin
membership, and the entry time of `N` is `k` plus that of `M`. -/
lemma reach_shift {S : Set ℕ} {N M k : ℕ} (hk : T^[k] N = M) (hav : ∀ j < k, T^[j] N ∉ S)
    (hN : 0 < N) (hM : 0 < M) :
    (N ∈ Reach S ↔ M ∈ Reach S) ∧ (N ∈ Reach S → entry S N = k + entry S M) := by
  have back : ∀ i, T^[i] N ∈ S → k ≤ i ∧ T^[i - k] M ∈ S := by
    intro i hi
    have hki : k ≤ i := by
      by_contra h
      push Not at h
      exact hav i h hi
    refine ⟨hki, ?_⟩
    rw [← hk, ← Function.iterate_add_apply, show i - k + k = i by omega]
    exact hi
  refine ⟨⟨fun ⟨_, i, hi⟩ => ⟨hM, i - k, (back i hi).2⟩,
    fun ⟨_, i, hi⟩ => ⟨hN, i + k, by rw [Function.iterate_add_apply, hk]; exact hi⟩⟩, ?_⟩
  rintro ⟨_, i, hi⟩
  have hM' : ∃ j, T^[j] M ∈ S := ⟨i - k, (back i hi).2⟩
  have h1 : T^[entry S N] N ∈ S := iterate_entry ⟨i, hi⟩
  obtain ⟨hk1, h2⟩ := back _ h1
  have h3 : entry S M ≤ entry S N - k := entry_le h2
  have h4 : entry S N ≤ entry S M + k :=
    entry_le (by rw [Function.iterate_add_apply, hk]; exact iterate_entry hM')
  omega

/-! ## Merging classes -/

/-- The merging class of `n` is the `classSet` of its quotient class. -/
lemma mergeClass_eq_classSet (n : ℕ) :
    mergeClass n = classSet (Quotient.mk mergeSetoid n) := by
  ext m
  simp only [mergeClass, classSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hm, h⟩
    exact ⟨hm, Quotient.sound h⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, Quotient.exact h⟩

/-- Every point of `P_T(b)` merges with `b`. -/
lemma pred_subset_mergeClass (b : ℕ) : Pred T b ⊆ mergeClass b := by
  rintro n ⟨hn, k, hk⟩
  exact ⟨hn, k, 0, hk⟩

end CollatzCLT
