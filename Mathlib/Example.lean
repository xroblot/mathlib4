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

/-- The bridge from `QuadraticAlgebra ℚ 1 1`, where the ring of integers sits, to the standard
form `ℚ(√5)`: `algEquivDiscrZero` lands on `discr 1 1`, which is `5`. -/
noncomputable def sqrtFive : QuadraticAlgebra ℚ 1 1 ≃ₐ[ℚ] QuadraticAlgebra ℚ 5 0 :=
  (algEquivDiscrZero (1 : ℚ) 1).trans (equivOfEq (by norm_num [discr_def]) rfl)

-- an explicit computation: `ω` is the golden ratio, of norm `-1`, and the bridge sends it to
-- `(1 + √5) / 2` in the standard form
example : norm (ω : QuadraticAlgebra ℤ 1 1) = -1 := by simp [norm_def]

example : (ω : QuadraticAlgebra ℤ 1 1) * ω = 1 + ω := by ext <;> simp

example : algEquivDiscrZero (1 : ℚ) 1 ω = ⟨1 / 2, 1 / 2⟩ := by ext <;> simp
