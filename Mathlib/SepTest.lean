module
public import Mathlib.Sandbox

@[expose] public section

open Algebra Ideal
open scoped Pointwise

/-! ### The missing transport, stated in general -/

/-- Separability passes from an integral extension of domains to their fraction fields. -/
theorem Algebra.IsSeparable.of_isFractionRing
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [IsDomain A] [IsDomain B] [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [Algebra.IsSeparable A B] : Algebra.IsSeparable K L := sorry

/-! ### Its specialisation to residue fields, mirroring the `IsAlgebraic` instance of
`RingTheory/LocalRing/ResidueField/Instances.lean` (prime section) -/

section residue
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A) (q : Ideal B) [q.LiesOver p] [p.IsPrime] [q.IsPrime]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

instance residueField_isSeparable [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := sorry

end residue

/-! ### Sufficiency check: the general-prime version, using only the two `sorry`s above -/

section Ramification

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank'' [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p] [P.IsPrime]
    [HasSeparableResidueFieldsAt R S p] :
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

end Ramification
