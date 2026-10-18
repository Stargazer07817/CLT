import LeanClt

/-!
# Frozen statements and definitions

A regression test for the trusted surface of the formalization: the headline statements and the
definitions they unfold to. It is not imported by the library root, so `lake build` does not build
it. Check it with

    lake env lean tests/Verbatim.lean

which should finish with no errors.

* **Section A** copies, character for character, 66 definitions into the namespace
  `CollatzCLT.Verbatim`, in dependency order and under the `open`s of their source files. Inside
  that namespace names resolve to the copies, so the copies form a parallel world built only from
  Mathlib, except the copy of `pinnedK`, which uses the library's `Zval`, `ell` and `lawS`. They are
  62 of the definitions the statements of section C rest on, and four that appear in no statement:
  `tauK`, `mergeSetoid`, `classSet` and `pinnedK`.
* **Section B** checks `@Verbatim.X = @CollatzCLT.X` by `rfl` for each copy. Any change to a
  definition in the library, or to anything it unfolds to, that is not a definitional equality
  makes this file fail.
* **Section C** restates the 22 headline statements in the namespace `CollatzCLT.VerbatimStmt`,
  where names resolve to the library's definitions, and closes each with the library's theorem as
  a term, so the elaborator checks that the two statements are definitionally equal.

The statements of section C, followed through definition bodies (not through proofs), rest on 68
definitions of this library. The six not copied in section A are `renewalR`, `Zval`, `bet`, `ell`
and `lawS` (`LeanClt/Renewal/Defs.lean`) and `alpha` (`LeanClt/Transfer/Defs.lean`); read them in
the library.
-/

noncomputable section

/-! ## A. Verbatim copies of the definitions -/

namespace CollatzCLT
namespace Verbatim

section
-- LeanClt/Defs.lean
open Real Filter Topology

def T (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

def F (n : ℕ) : ℕ := if Even n then n / 2 else (3 * n + 1) / 2

def U (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)

def Pred (G : ℕ → ℕ) (b : ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, G^[k] n = b}

def PredU (b : ℕ) : Set ℕ := {n | 0 < n ∧ Odd n ∧ ∃ k, U^[k] n = b}

def hit (G : ℕ → ℕ) (b n : ℕ) : ℕ := sInf {k | G^[k] n = b}

open Classical in
def window (A : Set ℕ) (X : ℕ) : Finset ℕ := (Finset.Icc 1 X).filter (· ∈ A)

def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ((window A X).card : ℝ) / X) atTop (𝓝 d)

def c : ℝ := log (4 / 3)

def κT : ℝ := 3 / c

def VT : ℝ := 2 * (log 3 + log 2) ^ 2 / c ^ 3

def κF : ℝ := 2 / c

def VF : ℝ := 2 * (log 3) ^ 2 / c ^ 3

def κU : ℝ := 1 / c

def VU : ℝ := 2 * (log 2) ^ 2 / c ^ 3

def Φ (z : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z

open Classical in
def CLTOn (A : Set ℕ) (stat : ℕ → ℕ → ℝ) : Prop :=
  ∀ z : ℝ, Tendsto (fun X : ℕ =>
      (((window A X).filter (fun n => stat X n ≤ z)).card : ℝ) / (window A X).card)
    atTop (𝓝 (Φ z))

def normalised (τ : ℕ → ℕ) (κ V : ℝ) (X n : ℕ) : ℝ :=
  ((τ n : ℝ) - κ * log n) / sqrt (V * log X)

end

section
-- LeanClt/Renewal/Defs.lean
open Real Finset Complex

def θ : ℝ := Real.log 3 / Real.log 2

def distZ (x : ℝ) : ℝ := |x - round x|

def IrrMeasure (d ϰ : ℝ) : Prop :=
  0 < d ∧ 1 ≤ ϰ ∧ ∀ h : ℕ, 1 ≤ h → d * (h : ℝ) ^ (-ϰ) ≤ distZ (h * θ)

end

section
-- LeanClt/Elementary/Affine.lean
open Function Finset

def wsum (a : ℕ → ℕ) (r : ℕ) : ℕ := ∑ i ∈ range r, a i

end

section
-- LeanClt/Elementary/Flow.lean
open Function

def IsPeriodic (n : ℕ) : Prop := ∃ p, 0 < p ∧ T^[p] n = n

def Merge (m n : ℕ) : Prop := ∃ i j, T^[i] m = T^[j] n

end

section
-- LeanClt/Transfer/Defs.lean
open Real Finset Complex

def words (n s : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.Nat.antidiagonalTuple n s).filter (fun a => ∀ i, 1 ≤ a i)

def half (n : ℕ) : ZMod (3 ^ n) := (2 : ZMod (3 ^ n))⁻¹

def psum {n : ℕ} (a : Fin n → ℕ) (j : Fin n) : ℕ := ∑ i : Fin n, if i ≤ j then a i else 0

end

section
-- LeanClt/Transfer/Typical.lean
open Real Finset

def ext {n : ℕ} (a : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then a ⟨i, h⟩ else 1

end

section
-- LeanClt/Mixing/Imports.lean
open Real Finset Complex

def chiZ {n : ℕ} (ξ x : ZMod (3 ^ n)) : ℂ :=
  cexp (((-(2 * π * ((ξ * x).val : ℝ) / 3 ^ n)) : ℝ) * I)

def fTao {n : ℕ} (ξ x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b - 1 : ℕ) : ℂ)⁻¹ * ∑ a ∈ Icc 1 (b - 1), chiZ ξ (x * (2 ^ a + 3))

def pairSum {n : ℕ} (a : Fin n → ℕ) (j : ℕ) : ℕ := ext a (2 * j) + ext a (2 * j + 1)

def majorantAt {n : ℕ} (ξ : ZMod (3 ^ n)) (a : Fin n → ℕ) : ℝ :=
  ∏ j ∈ range (n / 2),
    ‖fTao ξ ((3 : ZMod (3 ^ n)) ^ (2 * j) * half n ^ wsum (ext a) (2 * j + 2)) (pairSum a j)‖

def taoMajorant (n : ℕ) (ξ : ZMod (3 ^ n)) : ℝ :=
  ∑' S : ℕ, ∑ a ∈ words n S, (1 / 2 : ℝ) ^ S * majorantAt ξ a

def TaoMajorant : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ ξ : ZMod (3 ^ n), ¬ 3 ∣ ξ.val →
    taoMajorant n ξ ≤ C * (n : ℝ) ^ (-B)

def XmodN (n : ℕ) {p : ℕ} (a : Fin p → ℕ) : ZMod (3 ^ n) :=
  ∑ j : Fin p, (3 : ZMod (3 ^ n)) ^ (j : ℕ) * half n ^ psum a j

def prefixOf {p p' : ℕ} (h : p ≤ p') (w : Fin p' → ℕ) : Fin p → ℕ := fun i => w (Fin.castLE h i)

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

end

section
-- LeanClt/Exceptional/Defs.lean
open Real

def entry (S : Set ℕ) (n : ℕ) : ℕ := sInf {k | T^[k] n ∈ S}

def Reach (S : Set ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, T^[k] n ∈ S}

def AK (K : ℕ) : Set ℕ := {n | 0 < n ∧ ∃ k, T^[k] n ≤ K}

def tauK (K : ℕ) (n : ℕ) : ℕ := sInf {k | T^[k] n ≤ K}

def fwdOrbit (a : ℕ) : Set ℕ := Set.range (fun j => T^[j] a)

def NonRepeating (a : ℕ) : Prop := Function.Injective (fun j => T^[j] a)

def rayIndex (a n : ℕ) : ℕ := sInf {j | T^[entry (fwdOrbit a) n] n = T^[j] a}

def mergeClass (n : ℕ) : Set ℕ := {m | 0 < m ∧ Merge m n}

def mergeSetoid : Setoid ℕ := ⟨Merge, merge_equivalence⟩

def classSet (C : Quotient mergeSetoid) : Set ℕ :=
  {m | 0 < m ∧ Quotient.mk mergeSetoid m = C}

def Exc : Set ℕ := {n | 0 < n ∧ n ∉ Pred T 1}

def RefChoice (ref : ℕ → ℕ) : Prop :=
  (∀ n, 0 < n → 0 < ref n ∧ Merge (ref n) n) ∧
  (∀ m n, 0 < m → 0 < n → Merge m n → ref m = ref n) ∧
  (∀ n, 0 < n → (∃ p, 0 < p ∧ Merge p n ∧ IsPeriodic p) → IsPeriodic (ref n))

def eps (ref : ℕ → ℕ) (n : ℕ) : ℕ := entry (fwdOrbit (ref n)) n

end

section
-- LeanClt/Exceptional/Rays.lean
open Real Filter Topology Finset

def RayEntryLaw (a : ℕ) : Prop :=
  ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
  ∃ h : ℕ → ℝ, (∀ j, HasDensity (Pred T (T^[j] a)) (h j)) ∧ Monotone h ∧
    Tendsto h atTop (𝓝 pC) ∧
    (∀ j : ℕ, Tendsto (fun X : ℕ =>
      (((window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j)).card : ℝ) /
        (window (mergeClass a) X).card) atTop (𝓝 (h j / pC))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ j0 : ℕ, ∀ᶠ X : ℕ in atTop,
      (((window (mergeClass a) X).filter (fun n => j0 < rayIndex a n)).card : ℝ) ≤
        ε * (window (mergeClass a) X).card) ∧
    CLTOn (mergeClass a) (normalised (entry (fwdOrbit a)) κT VT)

def RayJointLaw (a : ℕ) : Prop :=
  ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
  ∃ h : ℕ → ℝ, (∀ j, HasDensity (Pred T (T^[j] a)) (h j)) ∧ Tendsto h atTop (𝓝 pC) ∧
    ∀ (j : ℕ) (z : ℝ), Tendsto (fun X : ℕ =>
      (((window (mergeClass a) X).filter (fun n => rayIndex a n ≤ j ∧
          ((entry (fwdOrbit a) n : ℝ) - κT * Real.log X) / √(VT * Real.log X) ≤ z)).card : ℝ) /
        (window (mergeClass a) X).card) atTop (𝓝 (h j / pC * Φ z))

def RayMovingLaw (a : ℕ) : Prop :=
  ∀ jX : ℕ → ℕ, Tendsto jX atTop atTop →
    Tendsto (fun X : ℕ => ((window (Pred T (T^[jX X] a)) X).card : ℝ) /
      (window (mergeClass a) X).card) atTop (𝓝 1) ∧
    ∀ z : ℝ, Tendsto (fun X : ℕ =>
      (((window (Pred T (T^[jX X] a)) X).filter (fun n =>
          ((hit T (T^[jX X] a) n : ℝ) - jX X - κT * Real.log n) / √(VT * Real.log X) ≤ z)).card
            : ℝ) / (window (Pred T (T^[jX X] a)) X).card) atTop (𝓝 (Φ z))

end

section
-- LeanClt/Main/VariantDefs.lean
open Real Filter Topology ProbabilityTheory MeasureTheory

open Classical in
def dyWindow (A : Set ℕ) (X : ℝ) : Finset ℕ := (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (· ∈ A)

open Classical in
def CLTOnDy (A : Set ℕ) (stat : ℝ → ℕ → ℝ) : Prop :=
  ∀ z : ℝ, Tendsto (fun X : ℝ =>
      (((dyWindow A X).filter (fun n => stat X n ≤ z)).card : ℝ) / (dyWindow A X).card)
    atTop (𝓝 (Φ z))

open Classical in
def JointLaw {ι : Type*} (L : Filter ι) (W : ι → Finset ℕ) (S₁ S₂ S₃ : ι → ℕ → ℝ)
    (a₁ a₂ a₃ : ℝ) : Prop :=
  ∀ z₁ z₂ z₃ : ℝ, Tendsto (fun i =>
      (((W i).filter (fun n => S₁ i n ≤ z₁ ∧ S₂ i n ≤ z₂ ∧ S₃ i n ≤ z₃)).card : ℝ) / (W i).card)
    L (𝓝 ((gaussianReal 0 1).real {w : ℝ | a₁ * w ≤ z₁ ∧ a₂ * w ≤ z₂ ∧ a₃ * w ≤ z₃}))

def HasOddDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => ((window {n | n ∈ A ∧ Odd n} X).card : ℝ) / (window {n | Odd n} X).card)
    atTop (𝓝 d)

end

section
-- LeanClt/Potential/Defs.lean
open Real Filter Topology Finset

def natDens (A : Set ℕ) : ℝ :=
  limUnder atTop (fun X : ℕ => ((window A X).card : ℝ) / X)

def hpot (n : ℕ) : ℝ := natDens (Pred T n)

end

section
-- LeanClt/Applications/Kernel.lean
open Real Filter Topology Finset Complex

def pinnedK (ρ η : ℕ) (h : ℤ) (u : ℝ) : ℝ :=
  ∑' t : ℕ, ∑' A : ℕ,
    if 0 ≤ Zval t A - u ∧ Zval t A - u ≤ ell ∧ ((ρ * A + η * t : ℕ) : ℤ) = h then
      lawS t A * Real.exp (Zval t A - u)
    else 0

end

section
-- LeanClt/Applications/Coordinates.lean
open Function

def coordT (a n : ℕ) : ℤ := (rayIndex a n : ℤ) - (entry (fwdOrbit a) n : ℤ)

def fwdOrbitF (a : ℕ) : Set ℕ := Set.range (fun j => F^[j] a)

def entryF (S : Set ℕ) (n : ℕ) : ℕ := sInf {k | F^[k] n ∈ S}

def rayIndexF (a n : ℕ) : ℕ := sInf {j | F^[entryF (fwdOrbitF a) n] n = F^[j] a}

def coordF (a n : ℕ) : ℤ := (rayIndexF a n : ℤ) - (entryF (fwdOrbitF a) n : ℤ)

end

section
-- LeanClt/Applications/AntiConc.lean
open Real Filter Topology Finset

def levelCount (S : Set ℕ) (f : ℕ → ℤ) (j : ℤ) (X : ℕ) : ℕ :=
  ((window S X).filter (fun n => f n = j)).card

end

end Verbatim

/-! ## B. Each copy agrees with the tree, by `rfl` -/

example : @Verbatim.T = @CollatzCLT.T := rfl
example : @Verbatim.F = @CollatzCLT.F := rfl
example : @Verbatim.U = @CollatzCLT.U := rfl
example : @Verbatim.Pred = @CollatzCLT.Pred := rfl
example : @Verbatim.PredU = @CollatzCLT.PredU := rfl
example : @Verbatim.hit = @CollatzCLT.hit := rfl
example : @Verbatim.window = @CollatzCLT.window := rfl
example : @Verbatim.HasDensity = @CollatzCLT.HasDensity := rfl
example : @Verbatim.c = @CollatzCLT.c := rfl
example : @Verbatim.κT = @CollatzCLT.κT := rfl
example : @Verbatim.VT = @CollatzCLT.VT := rfl
example : @Verbatim.κF = @CollatzCLT.κF := rfl
example : @Verbatim.VF = @CollatzCLT.VF := rfl
example : @Verbatim.κU = @CollatzCLT.κU := rfl
example : @Verbatim.VU = @CollatzCLT.VU := rfl
example : @Verbatim.Φ = @CollatzCLT.Φ := rfl
example : @Verbatim.CLTOn = @CollatzCLT.CLTOn := rfl
example : @Verbatim.normalised = @CollatzCLT.normalised := rfl
example : @Verbatim.θ = @CollatzCLT.θ := rfl
example : @Verbatim.distZ = @CollatzCLT.distZ := rfl
example : @Verbatim.IrrMeasure = @CollatzCLT.IrrMeasure := rfl
example : @Verbatim.wsum = @CollatzCLT.wsum := rfl
example : @Verbatim.IsPeriodic = @CollatzCLT.IsPeriodic := rfl
example : @Verbatim.Merge = @CollatzCLT.Merge := rfl
example : @Verbatim.words = @CollatzCLT.words := rfl
example : @Verbatim.half = @CollatzCLT.half := rfl
example : @Verbatim.psum = @CollatzCLT.psum := rfl
example : @Verbatim.ext = @CollatzCLT.ext := rfl
example : @Verbatim.chiZ = @CollatzCLT.chiZ := rfl
example : @Verbatim.fTao = @CollatzCLT.fTao := rfl
example : @Verbatim.pairSum = @CollatzCLT.pairSum := rfl
example : @Verbatim.majorantAt = @CollatzCLT.majorantAt := rfl
example : @Verbatim.taoMajorant = @CollatzCLT.taoMajorant := rfl
example : @Verbatim.TaoMajorant = @CollatzCLT.TaoMajorant := rfl
example : @Verbatim.XmodN = @CollatzCLT.XmodN := rfl
example : @Verbatim.prefixOf = @CollatzCLT.prefixOf := rfl
example : @Verbatim.TaoPrefix = @CollatzCLT.TaoPrefix := rfl
example : @Verbatim.entry = @CollatzCLT.entry := rfl
example : @Verbatim.Reach = @CollatzCLT.Reach := rfl
example : @Verbatim.AK = @CollatzCLT.AK := rfl
example : @Verbatim.tauK = @CollatzCLT.tauK := rfl
example : @Verbatim.fwdOrbit = @CollatzCLT.fwdOrbit := rfl
example : @Verbatim.NonRepeating = @CollatzCLT.NonRepeating := rfl
example : @Verbatim.rayIndex = @CollatzCLT.rayIndex := rfl
example : @Verbatim.mergeClass = @CollatzCLT.mergeClass := rfl
example : @Verbatim.mergeSetoid = @CollatzCLT.mergeSetoid := rfl
example : @Verbatim.classSet = @CollatzCLT.classSet := rfl
example : @Verbatim.Exc = @CollatzCLT.Exc := rfl
example : @Verbatim.RefChoice = @CollatzCLT.RefChoice := rfl
example : @Verbatim.eps = @CollatzCLT.eps := rfl
example : @Verbatim.RayEntryLaw = @CollatzCLT.RayEntryLaw := rfl
example : @Verbatim.RayJointLaw = @CollatzCLT.RayJointLaw := rfl
example : @Verbatim.RayMovingLaw = @CollatzCLT.RayMovingLaw := rfl
example : @Verbatim.dyWindow = @CollatzCLT.dyWindow := rfl
example : @Verbatim.CLTOnDy = @CollatzCLT.CLTOnDy := rfl
example : @Verbatim.JointLaw = @CollatzCLT.JointLaw := rfl
example : @Verbatim.HasOddDensity = @CollatzCLT.HasOddDensity := rfl
example : @Verbatim.natDens = @CollatzCLT.natDens := rfl
example : @Verbatim.hpot = @CollatzCLT.hpot := rfl
example : @Verbatim.pinnedK = @CollatzCLT.pinnedK := rfl
example : @Verbatim.coordT = @CollatzCLT.coordT := rfl
example : @Verbatim.fwdOrbitF = @CollatzCLT.fwdOrbitF := rfl
example : @Verbatim.entryF = @CollatzCLT.entryF := rfl
example : @Verbatim.rayIndexF = @CollatzCLT.rayIndexF := rfl
example : @Verbatim.coordF = @CollatzCLT.coordF := rfl
example : @Verbatim.levelCount = @CollatzCLT.levelCount := rfl

/-! ## C. The headline statements, restated verbatim and closed by the tree's theorems -/

namespace VerbatimStmt

section TheoremOneOne
-- LeanClt/Statements.lean
open Real

theorem density_pos (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    (∃ d > 0, HasDensity (Pred T b) d) ∧ (∃ d > 0, HasDensity (Pred F b) d) :=
  _root_.CollatzCLT.density_pos hTM hTP hθ b hb h3

theorem clt_T (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred T b) (normalised (hit T b) κT VT) :=
  _root_.CollatzCLT.clt_T hTM hTP hθ b hb h3

theorem clt_F (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred F b) (normalised (hit F b) κF VF) :=
  _root_.CollatzCLT.clt_F hTM hTP hθ b hb h3

theorem clt_U (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    CLTOn (PredU b) (normalised (hit U b) κU VU) :=
  _root_.CollatzCLT.clt_U hTM hTP hθ b hb h3

end TheoremOneOne

section Corollaries
-- LeanClt/Statements.lean, `section Corollaries`
open Real Filter Topology Finset

theorem dichotomy (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∃ dE : ℝ, HasDensity Exc dE ∧ dE < 1 ∧ (Exc.Nonempty → 0 < dE)) ∧
    (HasDensity (Pred T 1) 1 ↔ Exc = ∅) ∧
    (∀ b ∈ Exc, ¬ 3 ∣ b → Pred T b ⊆ Exc ∧ (∃ d > 0, HasDensity (Pred T b) d) ∧
      CLTOn (Pred T b) (normalised (hit T b) κT VT)) ∧
    (∀ b : ℕ, 0 < b → IsPeriodic b →
      (∃ d > 0, HasDensity (Reach (fwdOrbit b)) d) ∧
      CLTOn (Reach (fwdOrbit b)) (normalised (entry (fwdOrbit b)) κT VT)) ∧
    (∀ a : ℕ, 0 < a → NonRepeating a → RayEntryLaw a ∧ RayJointLaw a ∧ RayMovingLaw a) :=
  _root_.CollatzCLT.dichotomy hTM hTP hθ

open Classical in
theorem unconditional (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    {ref : ℕ → ℕ} (href : RefChoice ref) :
    (∀ n : ℕ, 0 < n → ∃ k, T^[k] n ∈ fwdOrbit (ref n)) ∧
    (∀ n0 : ℕ, 0 < n0 → ∃ pC : ℝ, HasDensity (mergeClass n0) pC ∧ ∀ z : ℝ,
      Tendsto (fun X : ℕ => ((((Icc 1 X).filter (fun n => n ∈ mergeClass n0 ∧
          normalised (eps ref) κT VT X n ≤ z)).card : ℝ) / X)) atTop (𝓝 (pC * Φ z))) ∧
    CLTOn {n | 0 < n} (normalised (eps ref) κT VT) ∧
    (∀ c0 : ℝ, HasDensity {n | 0 < n ∧ (eps ref n : ℝ) ≤ c0 * Real.log n}
      (if κT < c0 then 1 else if c0 = κT then 1 / 2 else 0)) ∧
    (∀ n ∈ Pred T 1, eps ref n ≤ hit T 1 n ∧ hit T 1 n ≤ eps ref n + 2) :=
  _root_.CollatzCLT.unconditional hTM hTP hθ href

end Corollaries

section CorollaryLemmas
-- LeanClt/Exceptional/Orbits.lean
open Function

theorem refChoice_exists : ∃ ref : ℕ → ℕ, RefChoice ref :=
  _root_.CollatzCLT.refChoice_exists

theorem ref_change {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (h : Merge a a') :
    ∃ B : ℕ, ∀ n : ℕ, 0 < n → Merge n a →
      entry (fwdOrbit a) n ≤ entry (fwdOrbit a') n + B ∧
      entry (fwdOrbit a') n ≤ entry (fwdOrbit a) n + B :=
  _root_.CollatzCLT.ref_change ha ha' h

end CorollaryLemmas

section Variants
-- LeanClt/Statements.lean, the closing sentence of Theorem 1.1 and later additions
open Real Filter Topology

theorem clt_T_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log X) / √(VT * log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log n) / √(VT * log X)) ∧
    CLTOnDy (Pred T b) (fun X n => ((hit T b n : ℝ) - κT * log X) / √(VT * log X)) :=
  _root_.CollatzCLT.clt_T_variants hTM hTP hθ b hb h3

theorem clt_F_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    CLTOn (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log X) / √(VF * log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log n) / √(VF * log X)) ∧
    CLTOnDy (Pred F b) (fun X n => ((hit F b n : ℝ) - κF * log X) / √(VF * log X)) :=
  _root_.CollatzCLT.clt_F_variants hTM hTP hθ b hb h3

theorem clt_U_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    CLTOn (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log X) / √(VU * log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log n) / √(VU * log X)) ∧
    CLTOnDy (PredU b) (fun X n => ((hit U b n : ℝ) - κU * log X) / √(VU * log X)) :=
  _root_.CollatzCLT.clt_U_variants hTM hTP hθ b hb h3

theorem joint_clocks (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log n) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log n) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log n) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) :=
  _root_.CollatzCLT.joint_clocks hTM hTP hθ b hb h3

theorem joint_clocks_variants (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ}
    (hθ : IrrMeasure d ϰ) (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    JointLaw atTop (window (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log X) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log X) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log X) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log n) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log n) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log n) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) ∧
    JointLaw atTop (dyWindow (PredU b))
      (fun X n => ((hit U b n : ℝ) - κU * log X) / √(log X))
      (fun X n => ((hit F b n : ℝ) - κF * log X) / √(log X))
      (fun X n => ((hit T b n : ℝ) - κT * log X) / √(log X))
      (√(2 / c ^ 3) * log 2) (√(2 / c ^ 3) * log 3) (√(2 / c ^ 3) * (log 3 + log 2)) :=
  _root_.CollatzCLT.joint_clocks_variants hTM hTP hθ b hb h3

theorem rates_T (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred T b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ c₀ * log n}
        (if κT < c₀ then p else if c₀ = κT then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ κT * log n + z * √(VT * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasDensity {n | n ∈ Pred T b ∧ (hit T b n : ℝ) ≤ (κT + η n) * log n} 0) :=
  _root_.CollatzCLT.rates_T hTM hTP hθ b hb h3

theorem rates_F (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasDensity (Pred F b) p ∧
      (∀ c₀ : ℝ, HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ c₀ * log n}
        (if κF < c₀ then p else if c₀ = κF then p / 2 else 0)) ∧
      (∀ z : ℝ, HasDensity
        {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ κF * log n + z * √(VF * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasDensity {n | n ∈ Pred F b ∧ (hit F b n : ℝ) ≤ (κF + η n) * log n} 0) :=
  _root_.CollatzCLT.rates_F hTM hTP hθ b hb h3

theorem rates_U (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : Odd b) (h3 : ¬ 3 ∣ b) :
    ∃ p > 0, HasOddDensity (PredU b) p ∧
      (∀ c₀ : ℝ, HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ c₀ * log n}
        (if κU < c₀ then p else if c₀ = κU then p / 2 else 0)) ∧
      (∀ z : ℝ, HasOddDensity
        {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ κU * log n + z * √(VU * log n)} (Φ z * p)) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atTop →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * log n} p) ∧
      (∀ η : ℝ → ℝ, Tendsto (fun x => η x * √(log x)) atTop atBot →
        HasOddDensity {n | n ∈ PredU b ∧ (hit U b n : ℝ) ≤ (κU + η n) * log n} 0) :=
  _root_.CollatzCLT.rates_U hTM hTP hθ b hb h3

end Variants

section Potential
-- LeanClt/Statements.lean
open Real Filter Topology Finset

theorem potential (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    (∀ n : ℕ, 0 < n → HasDensity (Pred T n) (hpot n)) ∧
    (∀ n : ℕ, 0 < n → (0 < hpot n ↔ ¬ 3 ∣ n)) ∧
    (∀ n : ℕ, 0 < n → ¬ IsPeriodic n →
      hpot n = hpot (2 * n) + (if n % 6 = 4 then hpot ((n - 1) / 3) else 0)) ∧
    (∀ v : ℕ → ℕ, (∀ j, 0 < v j) → Function.Injective v → (∀ j, T (v (j + 1)) = v j) →
      Tendsto (fun j => hpot (v j)) atTop (𝓝 0)) ∧
    (∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ K : ℕ, 2 ≤ K → ∃ f : ℕ → ℝ,
      (∃ w : ℕ → ℝ, ∀ n, f n =
        ∑ k ∈ (range (K + 1)).filter Odd, w k * (fwdOrbit k).indicator (fun _ => (1 : ℝ)) n) ∧
      (∀ n, 0 ≤ f n) ∧
      ∀ n : ℕ, 0 < n → 0 ≤ hpot n - f n ∧ hpot n - f n ≤ C * (Real.log K) ^ (-ε)) ∧
    (Tendsto hpot atTop (𝓝 0) ↔ ∀ n : ℕ, 0 < n → ∃ i, IsPeriodic (T^[i] n)) :=
  _root_.CollatzCLT.potential hTM hTP hθ

end Potential

section FixedFreq
-- LeanClt/Renewal/FixedFreq.lean
open Real Finset Complex MeasureTheory intervalIntegral Filter Topology

theorem fixedfreq {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) (ρ η : ℕ) (hco : Nat.Coprime ρ η)
    (Q₀ : ℕ) (hQ : 2 ≤ Q₀) :
    ∃ C : ℝ, ∀ r : ℤ, Int.gcd r Q₀ = 1 → ∀ u : ℝ, 2 ≤ u →
      ‖renewalR ρ η (2 * π * r / Q₀) u‖ ≤ C * u ^ (-(1 / (2 * (ϰ + 1)))) * Real.log u :=
  _root_.CollatzCLT.fixedfreq hθ ρ η hco Q₀ hQ

end FixedFreq

section AntiConc
-- LeanClt/Applications/AntiConc.lean
open Real Filter Topology Finset

open Classical in
theorem anticonc (hTM : TaoMajorant) (hTP : TaoPrefix) :
    ∃ C₀ X₀ : ℝ, 0 < C₀ ∧
    (∀ b : ℕ, 0 < b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (Pred T b) (fun n => (hit T b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      (levelCount (Pred F b) (fun n => (hit F b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ b : ℕ, Odd b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
      (levelCount (PredU b) (fun n => (hit U b n : ℤ)) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ X : ℕ, X₀ ≤ X → ∀ a : ℕ, 0 < a → NonRepeating a → ∀ j : ℤ,
      (levelCount (mergeClass a) (coordF a) j X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      (levelCount (mergeClass a) (coordT a) j X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ X : ℕ, X₀ ≤ X → ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ NonRepeating a) →
      (∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') → ∀ jC : ℕ → ℤ,
      ∑ a ∈ A, (levelCount (mergeClass a) (coordF a) (jC a) X : ℝ) ≤ C₀ * X / √(Real.log X) ∧
      ∑ a ∈ A, (levelCount (mergeClass a) (coordT a) (jC a) X : ℝ) ≤ C₀ * X / √(Real.log X)) ∧
    (∀ (S : Set ℕ) (p : ℝ), 0 < p → HasDensity S p →
      (∀ b : ℕ, 0 < b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
        (levelCount (S ∩ Pred T b) (fun n => (hit T b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X)) ∧
        (levelCount (S ∩ Pred F b) (fun n => (hit F b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X))) ∧
      (∀ b : ℕ, Odd b → ∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X → ∀ j : ℤ,
        (levelCount (S ∩ PredU b) (fun n => (hit U b n : ℤ)) j X : ℝ) / (window S X).card ≤
          C₀ / (p * √(Real.log X))) ∧
      (∃ X₁ : ℝ, ∀ X : ℕ, X₁ ≤ X →
        (∀ a : ℕ, 0 < a → NonRepeating a → ∀ j : ℤ,
          (levelCount (S ∩ mergeClass a) (coordF a) j X : ℝ) / (window S X).card ≤
            C₀ / (p * √(Real.log X)) ∧
          (levelCount (S ∩ mergeClass a) (coordT a) j X : ℝ) / (window S X).card ≤
            C₀ / (p * √(Real.log X))) ∧
        (∀ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ NonRepeating a) →
          (∀ a ∈ A, ∀ a' ∈ A, Merge a a' → a = a') → ∀ jC : ℕ → ℤ,
          (∑ a ∈ A, (levelCount (S ∩ mergeClass a) (coordF a) (jC a) X : ℝ)) /
            (window S X).card ≤ C₀ / (p * √(Real.log X)) ∧
          (∑ a ∈ A, (levelCount (S ∩ mergeClass a) (coordT a) (jC a) X : ℝ)) /
            (window S X).card ≤ C₀ / (p * √(Real.log X))))) :=
  _root_.CollatzCLT.anticonc hTM hTP

end AntiConc

section Escape
-- LeanClt/Applications/Escape.lean
open Real Filter Topology Finset

open Classical in
theorem escape (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ a : ℕ, 0 < a → NonRepeating a →
      ∃ pC : ℝ, 0 < pC ∧ HasDensity (mergeClass a) pC ∧
      (∃ X₀ : ℝ, ∀ K : ℕ, 1 ≤ K → ∀ X : ℕ, X₀ ≤ X → ∀ t : ℕ,
        (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K)).card : ℝ) /
          (window (mergeClass a) X).card ≤ C₀ / pC * K / √(Real.log X)) ∧
      (∀ K : ℕ → ℕ, Tendsto (fun X : ℕ => (K X : ℝ) / √(Real.log X)) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, ∀ t : ℕ,
          (((window (mergeClass a) X).filter (fun n => F^[t] n ≤ K X)).card : ℝ) /
            (window (mergeClass a) X).card ≤ ε) ∧
      (∀ K : ℕ, 1 ≤ K → ∃ dK : ℝ, HasDensity (AK K ∩ mergeClass a) dK ∧
        Tendsto (fun X : ℕ =>
          (((window (mergeClass a) X).filter (fun n => ∃ t, F^[t] n ≤ K)).card : ℝ) /
            (window (mergeClass a) X).card) atTop (𝓝 (dK / pC))) ∧
      (∀ dK : ℕ → ℝ, (∀ K : ℕ, 1 ≤ K → HasDensity (AK K ∩ mergeClass a) (dK K)) →
        Tendsto (fun K : ℕ => dK K / pC) atTop (𝓝 1)) :=
  _root_.CollatzCLT.escape hTM hTP hθ

end Escape

section Harmonic
-- LeanClt/Applications/Harmonic.lean
open Real Filter Topology Finset Complex

open Classical in
theorem harmonicfirsthit (hTM : TaoMajorant) (hTP : TaoPrefix) :
    (∃ C x₀ : ℝ, ∀ b : ℕ, 0 < b → ∀ x : ℝ, x₀ ≤ x → (b : ℝ) < x → ∀ m : ℕ,
      ∑ n ∈ (Icc ⌈2 * x ^ alpha⌉₊ ⌊x ^ (alpha ^ 2)⌋₊).filter
          (fun n => Odd n ∧ n ∈ Pred F b ∧ hit F b n = m), (1 : ℝ) / n ≤ C) ∧
    (∀ b : ℕ, 0 < b → ∃ C : ℝ, ∀ m : ℕ,
      ∑' n : ℕ, (if 0 < n ∧ n ∈ Pred F b ∧ hit F b n = m then (1 : ℝ) / n else 0) ≤
        C * Real.log (m + 2)) :=
  _root_.CollatzCLT.harmonicfirsthit hTM hTP

end Harmonic

section ModQ
-- LeanClt/Applications/ModQ.lean
open Real Filter Topology Finset Complex

theorem modq (hTM : TaoMajorant) (hTP : TaoPrefix) {d ϰ : ℝ} (hθ : IrrMeasure d ϰ)
    (b : ℕ) (hb : 0 < b) (h3 : ¬ 3 ∣ b) (Q₀ : ℕ) (hQ : 2 ≤ Q₀) :
    (∀ p : ℝ, HasDensity (Pred T b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ Pred T b ∧ ((hit T b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) ∧
    (∀ p : ℝ, HasDensity (Pred F b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ Pred F b ∧ ((hit F b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) ∧
    (Odd b → ∀ p : ℝ, HasDensity (PredU b) p → ∀ r₀ : ZMod Q₀,
      HasDensity {n | n ∈ PredU b ∧ ((hit U b n : ℕ) : ZMod Q₀) = r₀} (p / Q₀)) :=
  _root_.CollatzCLT.modq hTM hTP hθ b hb h3 Q₀ hQ

end ModQ

end VerbatimStmt

end CollatzCLT
