import LeanClt

/-!
# Axiom check for the headline theorems

    lake env lean tests/Axioms.lean

prints, for each of the 22 headline theorems, the axioms its proof depends on. Each line should read

    'CollatzCLT.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]

These are the three standard axioms of Lean's foundations. Anything else (`sorryAx`, an axiom
declared in this project, or `Lean.ofReduceBool` from `native_decide`) would mean that a proof is
not fully checked by the kernel; the final command then fails with an error.

The hypotheses `TaoMajorant`, `TaoPrefix` and `IrrMeasure d ϰ` are definitions of type `Prop`,
taken as explicit arguments, not axioms: they appear in the statements, not in this list.
-/

-- Theorem 1.1 (i)–(iii)
#print axioms CollatzCLT.density_pos
#print axioms CollatzCLT.clt_T
#print axioms CollatzCLT.clt_F
#print axioms CollatzCLT.clt_U
-- Theorem 1.1, closing sentence, and (iv)
#print axioms CollatzCLT.clt_T_variants
#print axioms CollatzCLT.clt_F_variants
#print axioms CollatzCLT.clt_U_variants
#print axioms CollatzCLT.joint_clocks
#print axioms CollatzCLT.joint_clocks_variants
-- Corollary 1.2
#print axioms CollatzCLT.rates_T
#print axioms CollatzCLT.rates_F
#print axioms CollatzCLT.rates_U
-- Corollaries 1.5 and 1.6, with the two lemmas Corollary 1.6 relies on
#print axioms CollatzCLT.dichotomy
#print axioms CollatzCLT.unconditional
#print axioms CollatzCLT.refChoice_exists
#print axioms CollatzCLT.ref_change
-- Theorem 1.4
#print axioms CollatzCLT.potential
-- Proposition 4.5, Theorem 6.10, Corollary 6.11, Proposition 6.12, Theorem 6.13
#print axioms CollatzCLT.fixedfreq
#print axioms CollatzCLT.anticonc
#print axioms CollatzCLT.escape
#print axioms CollatzCLT.harmonicfirsthit
#print axioms CollatzCLT.modq

-- The same check as a test: an error if any theorem uses an axiom outside the standard three.
open Lean in
#eval show CoreM Unit from do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let heads := [``CollatzCLT.density_pos, ``CollatzCLT.clt_T, ``CollatzCLT.clt_F,
    ``CollatzCLT.clt_U, ``CollatzCLT.clt_T_variants, ``CollatzCLT.clt_F_variants,
    ``CollatzCLT.clt_U_variants, ``CollatzCLT.joint_clocks, ``CollatzCLT.joint_clocks_variants,
    ``CollatzCLT.rates_T, ``CollatzCLT.rates_F, ``CollatzCLT.rates_U, ``CollatzCLT.dichotomy,
    ``CollatzCLT.unconditional, ``CollatzCLT.refChoice_exists, ``CollatzCLT.ref_change,
    ``CollatzCLT.potential, ``CollatzCLT.fixedfreq, ``CollatzCLT.anticonc, ``CollatzCLT.escape,
    ``CollatzCLT.harmonicfirsthit, ``CollatzCLT.modq]
  for h in heads do
    for a in ← collectAxioms h do
      unless allowed.contains a do
        throwError "{h} depends on the non-standard axiom {a}"
  logInfo m!"all {heads.length} headline theorems use only propext, Classical.choice and Quot.sound"
