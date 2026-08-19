module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Draft: `Algebra.HasSeparableResidueFieldsAt`

Prototype for the typeclass discussed on Zulip / in the review of #41591: a predicate saying that
the residue field extensions above a fixed prime `p` are separable. Only the fixed-`p` version for
now (the global version's correct shape is unclear outside the Dedekind setting; over all primes it
would also force `Frac B / Frac A` separable).

Design note: the condition is phrased on the quotient rings `A ⧸ p → B ⧸ P` rather than the
residue fields `κ(p) → κ(P)`. The two are equivalent (see
`RingTheory/LocalRing/ResidueField/Instances`), but the quotient version needs no
`Algebra κ(p) κ(P)` instance (which requires the localization scaffolding), so the class is free
to state; it also matches "refer to the rings" from the thread.
-/

@[expose] public section

open Ideal

attribute [local instance] Ideal.Quotient.field

/-- `Algebra.HasSeparableResidueFieldsAt A B p` states that for every prime `P` of `B` lying over
`p`, the residue field extension `κ(p) → κ(P)` is separable (phrased on the quotient rings). -/
class Algebra.HasSeparableResidueFieldsAt (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) [p.IsPrime] : Prop where
  isSeparable (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P)

/-- Backward-compat (maximal `p`): a perfect residue field `κ(p)`, with `B` integral over `A`,
gives the predicate. For maximal `p`, `A ⧸ p ≃ κ(p)` is a perfect field, so `B ⧸ P` (algebraic
over it) is separable directly, with no residue↔quotient bridge. -/
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) [p.IsMaximal] [PerfectField p.ResidueField] :
    Algebra.HasSeparableResidueFieldsAt A B p where
  isSeparable P := by
    intro _ _
    have : PerfectField (A ⧸ p) := .of_ringEquiv
      (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).symm
    have hp : P.under A = p := Ideal.LiesOver.over.symm
    have : P.IsMaximal := IsIntegral.isMaximal_of_isMaximal_comap P (hp.symm ▸ ‹p.IsMaximal›)
    infer_instance

/-- Finite residue field (e.g. an `HasFiniteQuotients` base at a nonzero prime) gives the
predicate: `A ⧸ p` is then a finite field, hence perfect, and `p` is automatically maximal. -/
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) [p.IsPrime] [Finite (A ⧸ p)] : Algebra.HasSeparableResidueFieldsAt A B p where
  isSeparable P := by
    intro _ _
    have : p.IsMaximal := Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain _)
    have hp : P.under A = p := Ideal.LiesOver.over.symm
    have : P.IsMaximal := IsIntegral.isMaximal_of_isMaximal_comap P (hp.symm ▸ ‹p.IsMaximal›)
    infer_instance

/-- An `HasFiniteQuotients` base gives the predicate at any nonzero prime `p`. -/
instance (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (p : Ideal A) [p.IsPrime] [NeZero p] [Ring.HasFiniteQuotients A] :
    Algebra.HasSeparableResidueFieldsAt A B p := by
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne p)
  infer_instance

/-! ### The class at work -/

/-- Inferred automatically for any integral extension of an HFQ base at a nonzero prime. -/
example (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    [Ring.HasFiniteQuotients A] (p : Ideal A) [p.IsPrime] [NeZero p] :
    Algebra.HasSeparableResidueFieldsAt A B p := inferInstance

/-- The class delivers exactly the residue-field separability that
`Ideal.card_inertia_eq_ramificationIdxIn` currently obtains from `[PerfectField p.ResidueField]`. -/
example (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsMaximal] [Algebra.HasSeparableResidueFieldsAt A B p]
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
    Algebra.IsSeparable p.ResidueField P.ResidueField := by
  have : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := Algebra.HasSeparableResidueFieldsAt.isSeparable P
  infer_instance

/-! ### `card_inertia_eq_ramificationIdxIn` via the class

Copies of `Galois.lean`'s three lemmas, with `[PerfectField p.ResidueField]` replaced by
`[HasSeparableResidueFieldsAt R S p]`. `PerfectField` is used in `card_stabilizer_eq_*` only to
supply `Algebra.IsSeparable p.ResidueField P.ResidueField` (the separable half of
`IsGalois κ(p) κ(P)`); the class supplies that instead, via the quotient↔residue bridge, once `p`,
`P` are maximal (so quotient = residue field). We therefore restrict to maximal `p` (and derive
maximality of `P` from integrality). -/

section Ramification

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise
open Algebra Ideal

attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [HasSeparableResidueFieldsAt R S p] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have : Algebra.IsSeparable (R ⧸ p) (S ⧸ P) := HasSeparableResidueFieldsAt.isSeparable P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [inertiaDeg_eq p P, ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

lemma ncard_primesOver_mul_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [HasSeparableResidueFieldsAt R S p] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) * P.inertiaDeg R = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank' p P,
    ← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

lemma card_inertia_eq_ramificationIdxIn' [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsMaximal] [P.IsPrime]
    [HasSeparableResidueFieldsAt R S p] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have hp : P.under R = p := Ideal.LiesOver.over.symm
  have : P.IsMaximal := IsIntegral.isMaximal_of_isMaximal_comap P (hp.symm ▸ ‹p.IsMaximal›)
  have H := ncard_primesOver_mul_card_inertia_mul_finrank' (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S ≠ 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

end Ramification

/-
# What goes wrong when generalizing `card_inertia_eq_ramificationIdxIn` via the class

Summary of the experiment above, for the record.

## What we did

`card_inertia_eq_ramificationIdxIn'` reproduces `Galois.lean`'s
`card_inertia_eq_ramificationIdxIn`, replacing the hypothesis `[PerfectField p.ResidueField]` by
`[HasSeparableResidueFieldsAt R S p]`. It compiles, together with its two supporting lemmas. The
proofs are unchanged except for one extra line in `card_stabilizer_eq_*` (feeding the class in) and
two in `card_inertia_*` (deriving `P.IsMaximal`), so they are slightly longer, not shorter.

## The problem: quotient rings versus residue fields

The proof of `card_stabilizer_eq_card_inertia_mul_finrank` needs the residue field extension
`κ(P) / κ(p)` to be separable (it is the separable half of `IsGalois κ(p) κ(P)`).

The class, as phrased, only provides separability of the quotient rings, `(S ⧸ P) / (R ⧸ p)`.

Now `κ(p) = Frac(R ⧸ p)`. So:
* when `p` is maximal, `R ⧸ p` is a field and equals `κ(p)`; the two separability statements are
  the same one, and the bridge instance in `RingTheory/LocalRing/ResidueField/Instances` transports
  one to the other. This is why that instance is stated only in its `maximal` section.
* when `p` is prime but not maximal, `R ⧸ p` is a proper subring of `κ(p) = Frac(R ⧸ p)`, and the
  two statements are genuinely different. The `prime` section of `Instances` provides only the
  `IsAlgebraic` bridge, not the `IsSeparable` one.

So to consume the class we had to strengthen `p` from prime to maximal (and derive `P` maximal from
integrality).

## Why the strengthening is a real cost

`card_inertia_eq_ramificationIdxIn`, and the identity `∑ e f = |G|` behind it
(`ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, `sum_ramification_inertia_eq_card`), are
stated and proved for an arbitrary prime `p`; none of them assumes `p` maximal.

In characteristic zero every residue field is perfect, so `PerfectField p.ResidueField` holds at
every prime, including non-maximal ones, where the ramification index can be `> 1`. The maximal
version cannot reach those primes. So the maximal version is not a generalization of the original:
it is incomparable, and drops primes the original covers.

(At the extreme `p = ⊥` the content is only `1 = 1`: there `e(⊥ ∣ ⊥) = 1` and `inertia = 1`. So
`⊥` itself is not the interesting lost case; the non-maximal *nonzero* primes in characteristic
zero are.)

## The missing piece

What would remove the maximality restriction is the transport

  `IsSeparable A B  →  IsSeparable (Frac A) (Frac B)`   (for an integral extension of domains),

which would give `κ(P) / κ(p)` separable from `(S ⧸ P) / (R ⧸ p)` at a general prime. It is true
(a minimal polynomial over `Frac A` divides the image of the one over `A`, and a factor of a
separable polynomial is separable), but it is not in mathlib. Every such lemma there runs the other
way (assume separability of the fraction fields), and there is no prime-level `IsSeparable` bridge.

## Design options

1. Keep the class on the quotient rings, and accept that as a hypothesis for this lemma it is really
   a statement about *maximal* ideals (which is exactly the finite-residue-field /
   `HasFiniteQuotients` setting, where `p` is automatically maximal anyway).
2. Add the missing domain-to-fraction-field separability transport; then the quotient class delivers
   residue separability at every prime and the maximality assumption disappears.
3. Phrase the hypothesis directly as `[Algebra.IsSeparable p.ResidueField P.ResidueField]`. This is
   a true generalization of `PerfectField` (weaker, and keeps `p` prime), and is exactly what the
   proof uses. Its cost is that stating it requires carrying the localization data
   `[Algebra (Localization.AtPrime p) (Localization.AtPrime P)] [IsLiesOverAlgebra p P]` in the
   signature, since the algebra on the residue fields is deliberately not an instance; and the class
   then plays no role in this particular lemma.
-/
