module

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section
namespace IntermediateField.extendTop

def IntermediateField.extendTop {K L : Type*} (L' : Type*) [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L'] (S : IntermediateField K L) :
    IntermediateField K L' where
  __ := IntermediateField.map (Algebra.algHom K L L') S


def IntermediateField.extendTop.orderHom {K L : Type*} (L' : Type*) [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L'] :
    IntermediateField K L →o IntermediateField K L' where
  toFun S := IntermediateField.map (Algebra.algHom K L L') S
  monotone' := fun _ _ h ↦ map_mono (Algebra.algHom K L L') h



end IntermediateField.extendTop
