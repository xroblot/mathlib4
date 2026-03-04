import Mathlib.FieldTheory.IntermediateField.Basic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
    (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    {A B : Type*} [CommRing A] [Algebra A K] [Algebra A F] [IsScalarTower A K F]
    [CommRing B] [Algebra B F] [Algebra A B] [IsScalarTower A B F]

abbrev IntermediateField.extendTop : IntermediateField K M := F.map (Algebra.algHom K L M)

noncomputable def IntermediateField.extendTopMap : F →+* (F.extendTop M) :=
  F.equivMap (Algebra.algHom K L M)

example : True := by
  let F' := F.extendTop M
  let : Algebra F F' := (F.extendTopMap M).toAlgebra
  let : Algebra A F' := ((algebraMap K F').comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K F' := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra B F' := ((algebraMap F F').comp (algebraMap B F)).toAlgebra
  have : IsScalarTower B F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower F F' M := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K F F' := IsScalarTower.to₁₂₃ K F F' M
  have : IsScalarTower A F F' := IsScalarTower.to₁₃₄ A K F F'
  have : IsScalarTower A B F' := IsScalarTower.to₁₂₄ A B F F'
  trivial
