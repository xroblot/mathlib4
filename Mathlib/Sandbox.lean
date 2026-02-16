import Mathlib.NumberTheory.RamificationInertia.Galois

section misc

instance (M R S : Type*) {T : Type*} [SMul M R] [SMul M S] [SMul R S] [Monoid M]
    [SetLike T M] [SubmonoidClass T M] [h : SMulDistribClass M R S] (N : T) :
    SMulDistribClass N R S := ⟨fun g _ _ ↦ h.smul_distrib_smul g _ _⟩

open MulAction Pointwise in
@[simp]
theorem Ideal.subgroupOf_stabilizer {R : Type*} [Ring R] (I : Ideal R) {G : Type*} [Group G]
    [MulSemiringAction G R] (H : Subgroup G) :
    (stabilizer G I).subgroupOf H = stabilizer H I := Subgroup.toSubmonoid_inj.mp rfl

open IntermediateField in
theorem IsGalois.fixedField_eq_iff_fixingSubgroup_eq {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsGalois F E] [FiniteDimensional F E]
    (K : IntermediateField F E) (H : Subgroup Gal(E/F)) :
    fixedField H = K ↔ K.fixingSubgroup = H := by
  simp [← OrderIso.apply_eq_iff_eq IsGalois.intermediateFieldEquivSubgroup,
    fixingSubgroup_fixedField, eq_comm]

open IntermediateField in
theorem IsGaloisGroup.fixedPoints_of_isGaloisGroup (G K L : Type*) [Group G] [Field K] [Field L]
    [Algebra K L] [MulSemiringAction G L] (F : IntermediateField K L) [hGKL : IsGaloisGroup G K L]
    (H : Subgroup G) [hHFL : IsGaloisGroup H F L] :
    FixedPoints.intermediateField H = F := by
  refine IntermediateField.ext_iff.mpr fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := hHFL.isInvariant.isInvariant x hx
    exact a.prop
  · have := congr_arg (restrictScalars K) <| IsGaloisGroup.fixedPoints_eq_bot H F L
    rw [IntermediateField.restrictScalars_bot_eq_self] at this
    rwa [← this] at hx

theorem IsGaloisGroup.of_fixedPoints_eq (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L]
    [MulSemiringAction G L] (F : IntermediateField K L) [hGKL : IsGaloisGroup G K L]
    {H : Subgroup G} (hF : FixedPoints.intermediateField H = F) :
    IsGaloisGroup H F L := by
  rw [eq_comm] at hF
  convert IsGaloisGroup.subgroup G K L H

theorem IsGaloisGroup.subgroup_iff (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L]
    [MulSemiringAction G L] (F : IntermediateField K L) [hGKL : IsGaloisGroup G K L]
    (H : Subgroup G) :
    IsGaloisGroup H F L ↔ FixedPoints.intermediateField H = F :=
  ⟨fun _ ↦ fixedPoints_of_isGaloisGroup G K L F H, fun h ↦ of_fixedPoints_eq G K L F h⟩

@[to_additive]
noncomputable def Subgroup.subgroupOfEquiv {G : Type*} [Group G] (H K : Subgroup G) :
    subgroupOf H K ≃* (K ⊓ H : Subgroup G) where
  toFun := fun ⟨x, hx⟩ ↦ ⟨x, x.prop, hx⟩
  invFun := fun ⟨x, hx₁, hx₂⟩ ↦ ⟨⟨x, hx₁⟩, mem_subgroupOf.mpr hx₂⟩
  map_mul' := by simp [MulMemClass.mul_def]
  right_inv := Function.rightInverse_iff_comp.mpr <| by aesop
  left_inv := Function.leftInverse_iff_comp.mpr rfl

@[to_additive (attr := simp)]
theorem Subgroup.subgroupOfEquiv_coe_apply {G : Type*} [Group G] (H K : Subgroup G)
    (x : subgroupOf H K) :
    (Subgroup.subgroupOfEquiv H K x : G) = x := rfl

@[to_additive (attr := simp)]
theorem Subgroup.subgroupOfEquiv_symm_apply {G : Type*} [Group G] (H K : Subgroup G)
    (x : ↥(K ⊓ H)) :
    ((Subgroup.subgroupOfEquiv H K).symm x : G) = x := by
  unfold Subgroup.subgroupOfEquiv
  aesop

open Pointwise in
theorem Ideal.stabilizer_inertia {α : Type*} [Ring α] (G : Type*) [Group G] [MulSemiringAction G α]
    (I : Ideal α) :
    MulAction.stabilizer (I.inertia G) I = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun x ↦ I.inertia_le_stabilizer x.prop

@[simp]
theorem AddSubgroup.inertia_inertia {M : Type*} [AddGroup M] (I : AddSubgroup M) (G : Type*)
    [Group G] [MulAction G M] :
    I.inertia (I.inertia G) = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun x ↦ x.prop

open Pointwise in
theorem Ideal.inertia_inertia {α : Type*} [Ring α] (G : Type*) [Group G] [MulSemiringAction G α]
    (I : Ideal α) :
    I.inertia (I.inertia G) = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun x ↦ x.prop

@[simp]
theorem IsGalois.fixingSubgroup_fixedPoints {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (H : Subgroup Gal(L/K)) :
    IntermediateField.fixingSubgroup
      (FixedPoints.intermediateField H : IntermediateField K L) = H := by
  rw [← OrderDual.toDual_inj]
  rw [← IsGalois.intermediateFieldEquivSubgroup.symm.apply_eq_iff_eq]
  rw [intermediateFieldEquivSubgroup_symm_apply]
  rw [OrderDual.ofDual_toDual]
  exact fixedField_fixingSubgroup (FixedPoints.intermediateField H)

theorem IsGaloisGroup.congr {G H K L : Type*} [Group G] [Group H] [CommSemiring K] [Semiring L]
    [Algebra K L]
    [MulSemiringAction G L] [MulSemiringAction H L] [hG : IsGaloisGroup G K L] (e : H ≃* G)
    (he : ∀ (h : H) (x : L), (e h) • x = h • x) :
    IsGaloisGroup H K L where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : L), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

theorem IsGaloisGroup.of_mulEquiv_algEquiv' {G K L : Type*} [Group G] [Field K] [Field L]
    [Algebra K L] [MulSemiringAction G L] [IsGalois K L] (e : G ≃* Gal(L/K))
    (he : ∀ (g : G) (x : L), (e g) x = g • x) :
    IsGaloisGroup G K L := IsGaloisGroup.congr e he

theorem Nat.eq_eq_of_mul_le_mul {a b c d : ℕ} (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hd : 0 < d)
    (h : c * d ≤ a * b) : a = c ∧ b = d :=
  ⟨le_antisymm ha <| Nat.le_of_mul_le_mul_right (h.trans <| Nat.mul_le_mul_left a hb) hd,
    le_antisymm hb <| Nat.le_of_mul_le_mul_left (h.trans <| Nat.mul_le_mul_right b ha) hc⟩

theorem Ideal.inertiaDeg_le_inertiaDeg {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Finite R T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P] [p.IsMaximal] :
    Ideal.inertiaDeg P Q ≤ Ideal.inertiaDeg p Q := by
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  unfold Ideal.inertiaDeg
  rw [dif_pos (by rwa [← Ideal.under_def, eq_comm, ← Ideal.liesOver_iff]),
    dif_pos (by rwa [← Ideal.under_def, eq_comm, ← Ideal.liesOver_iff])]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _

theorem Ideal.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (p : Ideal R) (P : Ideal S) (Q : Ideal T) (f : R →+* S) (g : S →+* T)
    (hp : p = Ideal.comap f P) (h : BddAbove {n | map (g.comp f) p ≤ Q ^ n}) :
    Ideal.ramificationIdx g P Q ≤ Ideal.ramificationIdx (g.comp f) p Q := by
  unfold Ideal.ramificationIdx
  refine csSup_le_csSup' h fun n hn ↦ ?_
  rw [Set.mem_setOf_eq, ← map_map, map_le_iff_le_comap, map_le_iff_le_comap, hp]
  apply Ideal.comap_mono
  rwa [← Ideal.map_le_iff_le_comap]

theorem Ideal.IsDedekindDomain.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.IsTorsionFree R T] [IsDomain R] [IsDedekindDomain T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T) [Q.LiesOver p] [P.LiesOver p] [Q.IsPrime]
    (hp : p ≠ ⊥) :
    Ideal.ramificationIdx (algebraMap S T) P Q ≤ Ideal.ramificationIdx (algebraMap R T) p Q := by
  rw [IsScalarTower.algebraMap_eq R S T]
  refine Ideal.ramificationIdx_le_ramificationIdx p P Q (algebraMap R S) (algebraMap S T) ?_ ?_
  · rwa [← under_def, ← liesOver_iff]
  · rw [← IsScalarTower.algebraMap_eq R S T]
    suffices ramificationIdx (algebraMap R T) p Q ≠ 0 by
      contrapose! this
      exact ramificationIdx_eq_zero (by rwa [not_bddAbove_iff] at this)
    exact ramificationIdx_ne_zero_of_liesOver _ hp

open MulAction Pointwise in
/--
Docs.
-/
def Ideal.stabilizerEquiv {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) :
    stabilizer G I ≃* stabilizer H I := by
  refine { toEquiv := ?_, map_mul' := ?_ }
  · refine Equiv.subtypeEquiv e fun _ ↦ ?_
    simp [Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, he]
  · simp

open MulAction Pointwise in
@[simp]
theorem Ideal.stabilizerEquiv_apply {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) (g : stabilizer G I) (x : R) :
    stabilizerEquiv e he I g • x = g • x := by
  unfold stabilizerEquiv
  simp [subgroup_smul_def, ← he g x]

open MulAction Pointwise in
@[simp]
theorem Ideal.stabilizerEquiv_symm_apply {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) (h : stabilizer H I) (x : R) :
    (stabilizerEquiv e he I).symm h • x = h • x := by
  rw [← (stabilizerEquiv e he I).apply_symm_apply h, stabilizerEquiv_apply,
    (stabilizerEquiv e he I).apply_symm_apply]

def Ideal.inertiaEquiv {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) :
    inertia G I ≃* inertia H I := by
  refine { toEquiv := ?_, map_mul' := ?_ }
  · refine Equiv.subtypeEquiv e fun _ ↦ ?_
    simp [he]
  · simp

@[simp]
theorem Ideal.inertiaEquiv_apply {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) (g : inertia G I) (x : R) :
    inertiaEquiv e he I g • x = g • x := by
  unfold inertiaEquiv
  simp [MulAction.subgroup_smul_def, ← he g x]

@[simp]
theorem Ideal.inertiaEquiv_symm_apply {G H : Type*} [Group G] [Group H] {R : Type*} [Ring R]
    [MulSemiringAction G R] [MulSemiringAction H R] (e : G ≃* H)
    (he : ∀ (g : G) (x : R), (e g) • x = g • x) (I : Ideal R) (h : inertia H I) (x : R) :
    (inertiaEquiv e he I).symm h • x = h • x := by
  rw [← (inertiaEquiv e he I).apply_symm_apply h, inertiaEquiv_apply,
    (inertiaEquiv e he I).apply_symm_apply h]

end misc

noncomputable section

open MulAction Pointwise Ideal

variable (A K L : Type*) {B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra K L] [Algebra A B]

variable {p : Ideal A} (P : Ideal B)

-- /--
-- Docs.
-- -/
-- def Ideal.stabilizerEquiv [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G] [Finite G]
--     [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B] [SMulDistribClass G B L]
--     [SMulDistribClass Gal(L/K) B L] :
--     stabilizer G P ≃* stabilizer Gal(L/K) P := by
--   refine { toEquiv := ?_, map_mul' := ?_ }
--   · refine Equiv.subtypeEquiv (IsGaloisGroup.mulEquivAlgEquiv G K L) fun g ↦ ?_
--     have {g : G} {x : B} : (IsGaloisGroup.mulEquivAlgEquiv G K L) g • x = g • x := by
--       apply FaithfulSMul.algebraMap_injective B L
--       simp [algebraMap.smul]
--     simp [← map_inv, Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, this]
--   · simp

-- /--
-- Docs.
-- -/
-- def Ideal.stabilizerEquiv' [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G] [Finite G]
--     [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B] [SMulDistribClass G B L]
--     [SMulDistribClass Gal(L/K) B L] :
--     stabilizer G P ≃* stabilizer Gal(L/K) P := by
--   refine { toEquiv := ?_, map_mul' := ?_ }
--   · refine Equiv.subtypeEquiv (IsGaloisGroup.mulEquivAlgEquiv G K L) fun g ↦ ?_
--     have {g : G} {x : B} : (IsGaloisGroup.mulEquivAlgEquiv G K L) g • x = g • x := by
--       apply FaithfulSMul.algebraMap_injective B L
--       simp [algebraMap.smul]
--     simp [← map_inv, Ideal.ext_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, this]
--   · simp

-- @[simp]
-- theorem Ideal.stabilizerEquiv_apply [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G]
--     [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
--     [SMulDistribClass G B L] [SMulDistribClass Gal(L/K) B L] (g : stabilizer G P) (x : L) :
--     stabilizerEquiv K L P G g • x = g • x := rfl

-- @[simp]
-- theorem Ideal.stabilizerEquiv_symm_apply [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G]
--     [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
--     [SMulDistribClass G B L] [SMulDistribClass Gal(L/K) B L] (g : stabilizer Gal(L/K) P) (x : L) :
--     (stabilizerEquiv K L P G).symm g • x = g • x := by
--   rw [← (stabilizerEquiv K L P G).apply_symm_apply g, stabilizerEquiv_apply,
--     (stabilizerEquiv K L P G).apply_symm_apply g]

-- /--
-- Docs.
-- -/
-- def Ideal.inertiaEquiv [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G] [Finite G]
--     [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B] [SMulDistribClass G B L]
--     [SMulDistribClass Gal(L/K) B L] :
--     inertia G P ≃* inertia Gal(L/K) P := by
--   refine { toEquiv := ?_, map_mul' := ?_ }
--   · refine Equiv.subtypeEquiv (IsGaloisGroup.mulEquivAlgEquiv G K L) fun g ↦ ?_
--     have {g : G} {x : B} : (IsGaloisGroup.mulEquivAlgEquiv G K L) g • x = g • x := by
--       apply FaithfulSMul.algebraMap_injective B L
--       simp [algebraMap.smul]
--     simp [this]
--   · simp

-- @[simp]
-- theorem Ideal.inertiaEquiv_apply [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G]
--     [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
--     [SMulDistribClass G B L] [SMulDistribClass Gal(L/K) B L] (g : inertia G P) (x : L) :
--     inertiaEquiv K L P G g • x = g • x := rfl

-- @[simp]
-- theorem Ideal.inertiaEquiv_symm_apply [Algebra B L] [FaithfulSMul B L] (G : Type*) [Group G]
--     [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
--     [SMulDistribClass G B L] [SMulDistribClass Gal(L/K) B L] (g : inertia Gal(L/K) P) (x : L) :
--     (inertiaEquiv K L P G).symm g • x = g • x := by
--   rw [← (inertiaEquiv K L P G).apply_symm_apply g, inertiaEquiv_apply,
--     (inertiaEquiv K L P G).apply_symm_apply g]

section general

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [CommRing 𝓞D] [Algebra 𝓞D B]

/-- Def. -/
@[mk_iff]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

/-- Def. -/
@[mk_iff]
class IsDecompositionRing extends
    IsGaloisGroup (stabilizer (B ≃ₐ[A] B) P) 𝓞D B

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [CommRing 𝓞E] [Algebra 𝓞E B]

/-- Def. -/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

/-- Def. -/
@[mk_iff]
class IsInertiaRing extends
    IsGaloisGroup (inertia (B ≃ₐ[A] B) P) 𝓞E B

theorem IsDecompositionField.of_isGaloisGroup (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] [Algebra B L] [FaithfulSMul B L]
    [MulSemiringAction G B] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]
    [IsFractionRing B L]
    [IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D :=
  { toIsGaloisGroup := by
      refine IsGaloisGroup.congr
        (stabilizerEquiv (IsGaloisGroup.mulEquivAlgEquiv G K L) (fun g x ↦ ?_) P).symm fun h x ↦ ?_
      · apply FaithfulSMul.algebraMap_injective B L
        simp [algebraMap.smul]
      · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
        simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul, ← subgroup_smul_def,
          stabilizerEquiv_symm_apply] }

theorem IsInertiaField.of_isGaloisGroup (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [IsGaloisGroup G K L] [Algebra B L] [FaithfulSMul B L]
    [MulSemiringAction G B] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]
    [IsFractionRing B L]
    [IsGaloisGroup (inertia G P) D L] :
    IsInertiaField K L P D :=
  { toIsGaloisGroup := by
      refine IsGaloisGroup.congr
        (inertiaEquiv (IsGaloisGroup.mulEquivAlgEquiv G K L) (fun g x ↦ ?_) P).symm fun h x ↦ ?_
      · apply FaithfulSMul.algebraMap_injective B L
        simp [algebraMap.smul]
      · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
        simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul, ← subgroup_smul_def,
          inertiaEquiv_symm_apply] }

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

abbrev stabilizerEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    stabilizer (B ≃ₐ[A] B) P ≃* stabilizer Gal(L/K)  P :=
  stabilizerEquiv (galRestrict A K L B).symm
    (fun g x ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply]) P

/--
This cannot be an instance since Lean cannot infer `D`.
-/
theorem IsDecompositionRing.of_isDecompositionField [Algebra.IsAlgebraic K L] [Algebra 𝓞D D]
    [IsFractionRing 𝓞D D] [Algebra.IsIntegral 𝓞D B] [IsIntegrallyClosed 𝓞D] [IsFractionRing B L]
    [Algebra 𝓞D L] [IsScalarTower 𝓞D B L] [IsScalarTower 𝓞D D L] [IsDecompositionField K L P D] :
    IsDecompositionRing A P 𝓞D :=
  { toIsGaloisGroup :=
      have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
      IsGaloisGroup.congr (stabilizerEquivOfIsFractionRing A K L P) (by simp) }

abbrev inertiaEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    inertia (B ≃ₐ[A] B) P ≃* inertia Gal(L/K) P :=
  inertiaEquiv (galRestrict A K L B).symm
    (fun g x ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply, ]) P

/--
This cannot be an instance since Lean cannot infer `D`.
-/
theorem IsInertiaRing.of_isInertiaField [Algebra 𝓞E E] [IsFractionRing 𝓞E E]
    [Algebra.IsIntegral 𝓞E B] [IsIntegrallyClosed 𝓞E] [IsFractionRing B L]
    [Algebra.IsAlgebraic K L] [Algebra 𝓞E L] [IsScalarTower 𝓞E B L] [IsScalarTower 𝓞E E L]
    [IsInertiaField K L P E] :
    IsInertiaRing A P 𝓞E :=
  { toIsGaloisGroup :=
      have := IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) 𝓞E B E L
      IsGaloisGroup.congr (inertiaEquivOfIsFractionRing A K L P) (by simp) }

open NumberField in
instance [NumberField K] [NumberField L] [NumberField D] (P : Ideal (𝓞 L))
    [IsDecompositionField K L P D] [Algebra.IsAlgebraic K L] :
    IsDecompositionRing (𝓞 K) P (𝓞 D) :=
      IsDecompositionRing.of_isDecompositionField (𝓞 K) K L P D (𝓞 D)

open NumberField in
instance [NumberField K] [NumberField L] [NumberField E] (P : Ideal (𝓞 L))
    [IsInertiaField K L P E] [Algebra.IsAlgebraic K L] :
    IsInertiaRing (𝓞 K) P (𝓞 E) :=
      IsInertiaRing.of_isInertiaField (𝓞 K) K L P E (𝓞 E)

instance [IsGalois K L] :
    IsDecompositionField K L P
      (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) :=
  { toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P) }

instance [IsGalois K L] :
    IsInertiaField K L P
      (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) :=
  { toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P) }

theorem IsDecompositionRing.primesOver [IsDecompositionRing A P 𝓞D] [hP : P.IsPrime]
    [Finite (stabilizer (B ≃ₐ[A] B) P)]
    (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D] :
    primesOver 𝓟D B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer (B ≃ₐ[A] B) P)
  exact σ.prop

variable [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [P.IsMaximal] [P.LiesOver p] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

variable [FiniteDimensional K L] [IsDecompositionField K L P D] [IsInertiaField K L P E]

omit [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L] in
include K P in
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p hp]

omit [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L] in
include P L in
theorem IsDecompositionField.rank_right [Algebra K D] [IsScalarTower K D L] [p.IsMaximal]
    [IsGalois K L] (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

omit [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L] in
include K P in
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_inertia_eq_ramificationIdxIn p hp]

omit [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L] in
include P L in
theorem IsInertiaField.rank_right [Algebra K E] [IsScalarTower K E L] [p.IsMaximal] [IsGalois K L]
    (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGalois.card_aut_eq_finrank]

omit [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L] in
include P in
theorem IsInertiaField.rank_decompositionField [Algebra K D] [Algebra K E] [Algebra D E]
    [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] [p.IsMaximal] [IsGalois K L]
    (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact primesOver_ncard_ne_zero p B

variable [IsDedekindDomain 𝓞D] [Module.Finite 𝓞D B] [Module.IsTorsionFree 𝓞D B]
  [P.IsPrime] (𝓟D : Ideal 𝓞D) [𝓟D.IsMaximal] [hD : P.LiesOver 𝓟D] [IsDecompositionRing A P 𝓞D]

variable [FaithfulSMul B L]

variable (𝓟E : Ideal 𝓞E) [𝓟E.IsMaximal] [hE : P.LiesOver 𝓟E] [IsInertiaRing A P 𝓞E]

include K L D P in
theorem IsDecompositionRing.ramficationIdxIn_mul_inertiaDegIn (hp : p ≠ ⊥) (hP : 𝓟D ≠ ⊥) :
    ramificationIdxIn 𝓟D B * inertiaDegIn 𝓟D B = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B (stabilizer (B ≃ₐ[A] B) P)
  rw [primesOver A P 𝓞D, Set.ncard_singleton, one_mul] at this
  rw [this, Nat.card_congr (stabilizerEquivOfIsFractionRing A K L P).toEquiv,
    IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
    IsDecompositionField.rank_left A K L P D hp]

variable [Algebra A 𝓞D] [Module.IsTorsionFree A 𝓞D] [IsScalarTower A 𝓞D B]

include K L D P in
theorem IsDecompositionRing.ramificationIdxIn [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  have : 𝓟D ≠ ⊥ := by
    apply Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_
    (ramficationIdxIn_mul_inertiaDegIn A K L P D 𝓞D 𝓟D hp this).symm.le).1
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero Gal(L/K) hp
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero Gal(L/K)

include K L D P in
theorem IsDecompositionRing.inertiaDegIn [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : 𝓟D ≠ ⊥ := by
    apply Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_
    (ramficationIdxIn_mul_inertiaDegIn K L P D 𝓞D 𝓟D hp this).symm.le).2
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero Gal(L/K) hp
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero Gal(L/K)

include K L D P in
theorem IsDecompositionRing.ramificationIdx [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞D) p 𝓟D = 1 := by
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟D) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
      ramificationIdxIn K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · exact map_ne_bot_of_ne_bot hp
  · exact Ideal.map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟D).mp hD

include K L D P in
theorem IsDecompositionRing.inertiaDeg [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    inertiaDeg p 𝓟D = 1 := by
  have := inertiaDeg_algebra_tower p 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P), right_eq_mul₀] at this
  exact inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)

attribute [local instance] Ideal.Quotient.field

include K L in
omit [IsDedekindDomain B] in
theorem IsInertiaRing.inertiaDegIn [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)]
    [FiniteDimensional (𝓞E ⧸ 𝓟E) (B ⧸ P)] :
    inertiaDegIn 𝓟E B = 1 := by
  rw [inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDeg_algebraMap,
    ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia Gal(L/K) P) 𝓟E P).toEquiv]
  simp

include L K in
omit [IsDedekindDomain B] [P.IsMaximal] [𝓟E.IsMaximal] in
theorem IsInertiaRing.primesOver :
    primesOver 𝓟E B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟E P Q (inertia Gal(L/K) P)
  exact inertia_le_stabilizer _ σ.prop

include L K P in
theorem IsInertiaRing.ramificationIdxIn [IsDedekindDomain 𝓞E] [Module.Finite 𝓞E B]
    [Module.IsTorsionFree 𝓞E B] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  have : 𝓟E ≠ ⊥ := by
    rw [over_def P 𝓟E]
    exact under_ne_bot 𝓞E <| ne_bot_of_liesOver_of_ne_bot hp _
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this B (inertia Gal(L/K) P)
  rwa [primesOver K L P, Set.ncard_singleton, one_mul, inertiaDegIn K L P 𝓞E, mul_one,
    card_inertia_eq_ramificationIdxIn p hp] at this

variable [Algebra 𝓞D 𝓞E] [IsScalarTower 𝓞D 𝓞E B] [hED : 𝓟E.LiesOver 𝓟D]

include K L D in
theorem IsInertiaRing.inertiaDeg_decompositionRing [p.IsMaximal] [𝓟D.LiesOver p]
    [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)] [FiniteDimensional (𝓞E ⧸ 𝓟E) (B ⧸ P)] (hp : p ≠ ⊥) :
    inertiaDeg 𝓟D 𝓟E = p.inertiaDegIn B := by
  rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K), inertiaDeg_algebra_tower p 𝓟D P,
    inertiaDeg_algebra_tower 𝓟D 𝓟E P, ← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P),
    inertiaDegIn K L P, IsDecompositionRing.inertiaDeg K L P D 𝓞D 𝓟D hp, one_mul, mul_one]

include K L D P in
theorem IsInertiaRing.ramificationIdx_decompositionRing [IsDedekindDomain 𝓞E]
    [Module.IsTorsionFree 𝓞D 𝓞E] [Module.Finite 𝓞E B] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)]
    [Module.IsTorsionFree 𝓞E B]
    [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap 𝓞D 𝓞E) 𝓟D 𝓟E = 1 := by
  have hDnz : 𝓟D ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  have hEnz : 𝓟E ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hDnz _
  have := ramificationIdx_algebra_tower (p := 𝓟D) (P := 𝓟E) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
      IsDecompositionRing.ramificationIdxIn K L P D 𝓞D 𝓟D hp,
      ← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
      ramificationIdxIn K L P 𝓞E 𝓟E hp, right_eq_mul₀] at this
    exact ramificationIdxIn_ne_zero Gal(L/K) hp
  · exact map_ne_bot_of_ne_bot hEnz
  · exact map_ne_bot_of_ne_bot hDnz
  · exact Ideal.map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟E).mp hE

end general

namespace IntermediateField

open IntermediateField

variable [IsGalois K L] [FiniteDimensional K L] (F : IntermediateField K L)

theorem isDecompositionField_iff_fixingSubgroup :
    IsDecompositionField K L P F ↔ F.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [isDecompositionField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem isInertiaField_iff_fixingSubgroup :
    IsInertiaField K L P F ↔ F.fixingSubgroup = inertia Gal(L/K) P := by
  rw [isInertiaField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

variable (D E : IntermediateField K L) [IsDecompositionField K L P D] [IsInertiaField K L P E]

variable (F : IntermediateField K L) (𝓞F : Type*) [CommRing 𝓞F] [Algebra 𝓞F F]
  [Algebra 𝓞F B] (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F] [Algebra B L] [FaithfulSMul B L] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F B L] [IsScalarTower 𝓞F F L] [hSD : SMulDistribClass Gal(L/K) B L]

theorem isDecompositionField_sup [IsFractionRing 𝓞F F] [IsIntegralClosure B 𝓞F L] :
    letI := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    IsDecompositionField F L P (D ⊔ F : IntermediateField K L) := by
  rw [isDecompositionField_iff]
  let H : Subgroup Gal(L/K) := stabilizer Gal(L/K) P ⊓ F.fixingSubgroup
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup H ↥(D ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isDecompositionField_iff_fixingSubgroup K L P D).mp inferInstance]
  have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField Gal(L/K) K L F
  have : SMulDistribClass F.fixingSubgroup B L :=
    { smul_distrib_smul := fun g ↦ hSD.smul_distrib_smul g }
  let e : stabilizer Gal(L/F) P ≃* H :=
    (stabilizerEquiv F L P F.fixingSubgroup).symm.trans <|
      ((stabilizer F.fixingSubgroup P).equivMapOfInjective _
        F.fixingSubgroup.subtype_injective).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
  refine IsGaloisGroup.congr e fun g x ↦ ?_
  simpa only [subgroup_smul_def, AlgEquiv.smul_def] using
    Ideal.stabilizerEquiv_symm_apply F L P F.fixingSubgroup g x

theorem isInertiaField_sup [IsFractionRing 𝓞F F] [IsIntegralClosure B 𝓞F L] :
    letI := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    IsInertiaField F L P (E ⊔ F : IntermediateField K L) := by
  rw [isInertiaField_iff]
  let H : Subgroup Gal(L/K) := inertia Gal(L/K) P ⊓ F.fixingSubgroup
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup H ↥(E ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isInertiaField_iff_fixingSubgroup K L P E).mp inferInstance]
  have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField Gal(L/K) K L F
  have : SMulDistribClass F.fixingSubgroup B L :=
    { smul_distrib_smul := fun g ↦ hSD.smul_distrib_smul g }
  let e : inertia Gal(L/F) P ≃* H :=
    (inertiaEquiv F L P F.fixingSubgroup).symm.trans <|
      ((inertia F.fixingSubgroup P).equivMapOfInjective _
        F.fixingSubgroup.subtype_injective).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
  refine IsGaloisGroup.congr e fun g x ↦ ?_
  simpa only [subgroup_smul_def, AlgEquiv.smul_def] using
    Ideal.inertiaEquiv_symm_apply F L P F.fixingSubgroup g x

theorem isDecompositionField_le_of_primesOver_eq_singleton [P.IsPrime]
    (hF : primesOver 𝓟F B = {P}) : D ≤ F := by
  rw [← OrderIso.le_iff_le IsGalois.intermediateFieldEquivSubgroup,
    IsGalois.intermediateFieldEquivSubgroup_apply, IsGalois.intermediateFieldEquivSubgroup_apply,
    OrderDual.toDual_le_toDual,(isDecompositionField_iff_fixingSubgroup K L P D).mp inferInstance]
  intro g hg
  have : g • P ∈ 𝓟F.primesOver B := by
    refine ⟨IsPrime.smul g, ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    have hg : ∀ x ∈ F, g • x = x := hg
    have hg : ∀ x : 𝓞F, g⁻¹ • algebraMap 𝓞F B x = algebraMap 𝓞F B x := by
      intro x
      rw [inv_smul_eq_iff]
      apply FaithfulSMul.algebraMap_injective B L
      have (b : B) : algebraMap B L (g • b) = g • algebraMap B L b := algebraMap.coe_smul' g b L
      rw [this]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply 𝓞F F L, hg]
      norm_num
    rw [liesOver_iff, under_def]
    rw [Ideal.ext_iff]
    intro x
    rw [mem_comap]
    rw [mem_pointwise_smul_iff_inv_smul_mem, hg]
    rw [← mem_comap, ← under_def, (liesOver_iff P 𝓟F).mp inferInstance]
  rwa [hF] at this

variable [Algebra A 𝓞F] [IsScalarTower A 𝓞F B]

example [IsDedekindDomain 𝓞F] [Module.Finite 𝓞F B] [Module.IsTorsionFree 𝓞F B]
    [IsFractionRing 𝓞F F] [IsIntegralClosure B 𝓞F L] [𝓟F.LiesOver p]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [IsGaloisGroup Gal(L/K) A B] [𝓟F.IsMaximal]
    [Algebra.IsSeparable (𝓞F ⧸ 𝓟F) (B ⧸ P)]
    (hF₁ : ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1) (hF₂ : inertiaDeg p 𝓟F = 1) (hp : p ≠ ⊥)
    (hPF : 𝓟F ≠ ⊥) :
    F ≤ D := by
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := sorry
  have := isDecompositionField_sup K L P D F 𝓞F
  refine le_of_sup_eq' ?_
  rw [eq_comm]
  refine IntermediateField.eq_of_le_of_finrank_eq' le_sup_left ?_
  rw [IsDecompositionField.rank_left K L P D hp, IsDecompositionField.rank_left F L P ↥(D ⊔ F) hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K), inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ramificationIdx_algebra_tower (p := p) (P := 𝓟F) (Q := P), hF₁,
    inertiaDeg_algebra_tower p 𝓟F P, hF₂, one_mul, one_mul,
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F)]
  · sorry
  · sorry
  · sorry

#exit

  let M := F ⊔ LD
  let : Algebra F M := (inclusion le_sup_left).toRingHom.toAlgebra
  let : Algebra 𝓞F M := ((algebraMap F M).comp (algebraMap 𝓞F F)).toAlgebra
  let 𝓞M := integralClosure 𝓞F M
  let : Algebra A 𝓞M := sorry
  have : IsScalarTower 𝓞M M L := Subalgebra.isScalarTower_left 𝓞M
  have : IsScalarTower 𝓞F M L := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    sorry
  have : IsScalarTower 𝓞F 𝓞M L := by
    apply IsScalarTower.to₁₂₄ 𝓞F 𝓞M M L
  let : Algebra 𝓞M B := (IsIntegralClosure.lift 𝓞F B L).toRingHom.toAlgebra
  have : IsScalarTower A 𝓞M B := sorry
  have : IsDedekindDomain 𝓞M := sorry
  let 𝓟M : Ideal 𝓞M := Ideal.comap (algebraMap 𝓞M B) P
  have t₀ := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K)

#exit

  have : ramificationIdx (algebraMap 𝓞M B) 𝓟M P = p.ramificationIdxIn B := by
    have := ramificationIdx_algebra_tower (p := 𝓟F) (P := 𝓟M) (Q := P) ?_ ?_ ?_

    sorry
  have : inertiaDeg 𝓟M P = p.inertiaDegIn B := sorry
  have : p.ramificationIdxIn B * p.inertiaDegIn B ≤ Module.finrank M L := sorry
  have : LD = M := by
    apply IntermediateField.eq_of_le_of_finrank_le'
    · exact le_sup_right
    · rwa [IsDecompositionField.rank_left K L P LD hp]
  exact le_of_sup_eq this.symm




end IntermediateField
