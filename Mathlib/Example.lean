module

public import Mathlib.Sandbox
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open QuadraticAlgebra Int

local instance : Fact (¬ IsSquare (discr (5 : ℚ) 0)) := ⟨by
  rw [discr_def]
  norm_num⟩

#synth NumberField (QuadraticAlgebra ℚ 5 0)

noncomputable example :
    QuadraticAlgebra ℤ 1 1 ≃ₐ[ℤ] integralClosure ℤ (QuadraticAlgebra ℚ 5 0) := by
  apply algEquivIntegralClosure'
  · rw [isFundamentalDiscr_iff_squarefree, discr_def]
    norm_num
  · exact ⟨IsUnit.unit (a := 1 / 2) (by norm_num), by simp [discr_def]; norm_num⟩
