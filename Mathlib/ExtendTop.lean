import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraTower
import Mathlib.MWE

namespace IntermediateField

variable {K L : Type*} (M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] (F : IntermediateField K L)

/--
Doscs.
-/
def extendTop : IntermediateField K M := F.map (Algebra.algHom K L M)

namespace ExtendTop

noncomputable instance algebra : Algebra F (F.extendTop M) :=
  (F.equivMap (Algebra.algHom K L M)).toRingHom.toAlgebra

instance : IsScalarTower F (F.extendTop M) M := IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower K F (F.extendTop M) := IsScalarTower.to₁₂₃ K F (F.extendTop M) M

variable (R S T : Type*) [CommSemiring S] [Algebra S F]

noncomputable instance algebra' : Algebra S (F.extendTop M) :=
  ((algebraMap F (F.extendTop M)).comp (algebraMap S F)).toAlgebra

-- Check there is no diamond
example : (algebra _ _ : Algebra F (F.extendTop M)) =
  (algebra' _ _ _ : Algebra F (F.extendTop M)) := rfl

-- There is one diamond possibility
example [CommRing R] [Algebra R K] [Algebra R M] [Algebra R L] [IsScalarTower R K L]
  [IsScalarTower R K M] : 1 = 0 := by
  let A : Algebra R (F.extendTop M) := (F.extendTop M).algebra'
  let B : Algebra R (F.extendTop M) := algebra' _ _ _
  have : A = B := rfl


instance : IsScalarTower S F (F.extendTop M) := IsScalarTower.of_algebraMap_eq' rfl

instance [Algebra S M] [IsScalarTower S F M] : IsScalarTower S (F.extendTop M) M :=
  IsScalarTower.to₁₃₄ S F (F.extendTop M) M

instance [CommSemiring R] [Algebra R K] [Algebra R F] :
    IsScalarTower R K (extendTop M F) := sorry

theorem isFractionRing [CommSemiring R] [Algebra R K] [Algebra R S] [Algebra R F] [Algebra R M]
    [IsScalarTower R S F] [IsScalarTower R K F] [IsScalarTower R K M] [IsFractionRing S F] :
    IsFractionRing S (F.extendTop M) :=
  .of_algEquiv _ _ _ <| ((F.equivMap (Algebra.algHom K L M)).restrictScalars R).extendScalars S

instance [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R K F] :
    IsIntegralClosure S R (F.extendTop M) := by
  let : Algebra R (F.extendTop M) := by exact algebra' M F R
  let f := @AlgEquiv.restrictScalars R K F (F.extendTop M) _ _ _ _ _ _ _ _ this _ _ (F.equivMap (Algebra.algHom K L M))
  let f := (F.equivMap (Algebra.algHom K L M)).restrictScalars R


end IntermediateField.ExtendTop

#lint
