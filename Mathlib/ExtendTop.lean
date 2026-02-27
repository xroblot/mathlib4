module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.MWE

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

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

-- Cannot be an instance because of possible diamond with `IntermediateField.algebra'`
noncomputable instance algebra' : Algebra S (F.extendTop M) :=
  ((algebraMap F (F.extendTop M)).comp (algebraMap S F)).toAlgebra

-- Check there is no diamond
example : (algebra _ _ : Algebra F (F.extendTop M)) =
  (algebra' _ _ _ : Algebra F (F.extendTop M)) := rfl

instance :
    letI := algebra' F M S
    IsScalarTower S F (F.extendTop M) :=
  let := algebra' F M S
  IsScalarTower.of_algebraMap_eq' rfl

instance instIsScalarTower' [Algebra S M] [IsScalarTower S F M] :
    IsScalarTower S (F.extendTop M) M := IsScalarTower.to₁₃₄ S F (F.extendTop M) M

instance [CommSemiring R] [Algebra R K] [Algebra R F] : IsScalarTower R K (F.extendTop M) := sorry

-- There is one diamond possibility
theorem aux [CommRing R] [Algebra R K] [Algebra R M] [Algebra R L] [IsScalarTower R K L]
    [IsScalarTower R K M] [IsScalarTower R F M] :
    ((F.extendTop M).algebra' : Algebra R (F.extendTop M)) =
      (algebra' F M R : Algebra R (F.extendTop M)) := by
  ext r x
  rw [SetLike.val_smul_of_tower, Algebra.smul_def, @Algebra.smul_def, MulMemClass.coe_mul,
    @IsScalarTower.algebraMap_apply R (F.extendTop M) M _ _ _ (algebra' F M R) _ _
    (instIsScalarTower' F M R) r]
  rfl

theorem isFractionRing [CommSemiring R] [Algebra R K] [Algebra R S] [Algebra R F] [Algebra R M]
    [IsScalarTower R S F] [IsScalarTower R K F] [IsScalarTower R K M] [IsFractionRing S F] :
    IsFractionRing S (F.extendTop M) :=
  .of_algEquiv _ _ _ <| ((F.equivMap (Algebra.algHom K L M)).restrictScalars R).extendScalars S

theorem isIntegralClosure [Algebra S M] [IsScalarTower S F M] [CommRing R] [Algebra R K] [Algebra R M] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R K M] [IsScalarTower R F M] [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendTop M) := by
  refine .of_algEquiv S R F (B' := F.extendTop M) ?_ ?_
  · convert (F.equivMap (Algebra.algHom K L M)).restrictScalars R
    exact (aux _ _ _).symm
  · ext x
    have := IsScalarTower.algebraMap_apply S (F.extendTop M) M x
    convert this.symm
    simp
  
    simp [extendTop]

    apply FaithfulSMul.algebraMap_injective _ M




variable (T : Type*) [CommRing T] [Algebra R T] [Algebra T L] [Algebra T M]

instance : Module.Finite T (integralClosure T M) := sorry

instance : Algebra R (integralClosure T M) :=
  ((algebraMap T _).comp (algebraMap R T)).toAlgebra

instance toto : IsScalarTower R T (integralClosure T M) := IsScalarTower.of_algebraMap_eq' rfl

instance [Module.Finite R T] : Module.Finite R (integralClosure T M) := by
  convert Module.Finite.trans T (integralClosure T M)
  infer_instance
  convert toto M R T
  ext
  sorry
  infer_instance



-- have : Module.IsTorsionFree A C₀ :






end IntermediateField.ExtendTop

#lint
