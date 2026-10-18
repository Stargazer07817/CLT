import LeanClt.Transfer.Adjacent

/-!
# §5 and §6.1–6.2: status

All statements of this draft file are now proved:

* `transfer` (5.14, `eq:transfer`): `Theorem.lean`;
* `transfer_scalar` (5.15, `eq:scalar`): `Scalar.lean`;
* `adjacent_of_transport` (Lemma 6.1): `Adjacent.lean`;
* the transport property for the three clocks: `Transport.lean`.

Each takes `JointMixing` (Theorem 3.1) as a hypothesis and, where a kernel is evaluated, Rhin's
measure `IrrMeasure d ϰ`. `JointMixing` itself is proved from the two Tao imports as
`jointMixing_of_tao` (`Mixing/Telescope.lean`).
-/
