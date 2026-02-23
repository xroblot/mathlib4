module

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

section

variable (A R B R' : Type*) [CommRing R] [CommSemiring A] [CommRing B] [Algebra R B]
  [Algebra A B] [CommRing R'] [Algebra R' B] [IsIntegralClosure A R B]

theorem IsIntegralClosure.of_mulEquiv (e : R' ≃+* R)
    (h : (algebraMap R B).comp e.toRingHom = algebraMap R' B) :
    IsIntegralClosure A R' B := by
  refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
  · exact IsIntegralClosure.algebraMap_injective A R B
  · simp_rw [RingEquiv.isIntegral_iff e h]
    exact IsIntegralClosure.isIntegral_iff

end

section

theorem IsIntegral.map_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {B C F : Type*}
    [Ring B] [Ring C] [Algebra R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C]
    [IsScalarTower R A C] [EquivLike F B C] [AlgEquivClass F A B C] {f : F} {b : B} :
    IsIntegral R (f b) ↔ IsIntegral R b :=
  ⟨fun h ↦ AlgEquiv.coe_coe_symm_apply_coe_apply f b ▸ map (AlgEquivClass.toAlgEquiv f).symm h,
    fun h ↦ map f h⟩

variable (A R B B' : Type*) [CommRing R] [CommSemiring A] [CommRing B] [Algebra R B]
  [Algebra A B] [CommRing B'] [Algebra R B'] [Algebra A B'] [IsIntegralClosure A R B]

theorem IsIntegralClosure.of_algEquiv (e : B ≃ₐ[R] B')
    (h : algebraMap A B' = e.toRingHom.comp (algebraMap A B)) :
    IsIntegralClosure A R B' := by
  refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
  · rw [h]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      EmbeddingLike.comp_injective]
    exact IsIntegralClosure.algebraMap_injective A R B
  · intro x
    have := IsIntegral.map_iff (f := e.symm) (b := x)  (R := R)
    rw [← this, IsIntegralClosure.isIntegral_iff (A := A) (R := R)]
    simp only [h, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      AlgEquiv.eq_symm_apply]

end

#exit

section

variable (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] [h : IsScalarTower M N α]

theorem IsScalarTower.of_equiv (N' : Type*) [SMul M N'] [SMul N' α] (e : N' ≃ N)
    (he₁ : ∀ (m : M) x, m • (e x) = e (m • x))
    (he₂ : ∀ (x : N') (a : α), (e x) • a = x • a) :
    IsScalarTower M N' α := by
  refine { smul_assoc := ?_ }
  intro m n' a
  have := h.smul_assoc m (e n') a
  rw [he₁] at this
  rwa [he₂, he₂] at this


variable (A B₁ B₂ C : Type*) [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C]
  [Algebra A B₁] [Algebra A B₂] [Algebra A C] [Algebra B₁ C] [Algebra B₂ C]
  [h : IsScalarTower A B₁ C]

theorem IsScalarTower.of_algEquiv (e : B₁ ≃ₐ[A] B₂)
    (he : ∀ x, algebraMap B₂ C (e x) = algebraMap B₁ C x) :
    IsScalarTower A B₂ C := by
  apply IsScalarTower.of_equiv A B₁ C B₂ e.symm.toEquiv ?_ ?_
  · intro a x
    simp
  · intro x a
    simpa [Algebra.algebraMap_eq_smul_one] using congr_arg (· • a) (he (e.symm x))






end
