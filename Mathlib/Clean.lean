import Mathlib

open nonZeroDivisors NumberField

example {K : Type*} [Field K] {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K]
    [IsFractionRing R₁ K] {I : FractionalIdeal R₁⁰ K} (hI : I ≠ 0) {x : K} :
    1 = 0 := by
  sorry

theorem differentIdeal_ne_zero (A K L B: Type*) [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [IsFractionRing B L] [NoZeroSMulDivisors A B] :
    differentIdeal A B ≠ 0 := by
  rw [← (FractionalIdeal.coeIdeal_injective (R := B) (K := L)).ne_iff]
  simp [coeIdeal_differentIdeal A K]

open IntermediateField IntermediateField.LinearDisjoint in
/-- Doc. -/
noncomputable def Basis.ofLinearDisjoint {F : Type*} {E : Type*}
    [Field F] [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F A]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι] [Finite ι]
    (b : Basis ι F B) :
    Basis ι A E :=
  have : Fintype ι := Fintype.ofFinite ι
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_right' h₁ b.linearIndependent)
    (mul_left_cancel₀ (Module.finrank_pos.ne' : Module.finrank F A ≠ 0) (by
      rw [← Module.finrank_eq_card_basis b, ← finrank_sup h₁,
        Module.finrank_mul_finrank, h₂, finrank_top']))

@[simp]
theorem Basis.ofLinearDisjoint_apply {F : Type*}
    {E : Type*} [Field F] [Field E] [Algebra F E] {A B : IntermediateField F E}
    [FiniteDimensional F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι]
    [Finite ι] (b : Basis ι F B) (i : ι) :
    b.ofLinearDisjoint h₁ h₂ i = algebraMap B E (b i) := by
  simp [Basis.ofLinearDisjoint]

@[simp]
theorem Basis.ofLinearDisjoint_repr_apply {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E}
    [FiniteDimensional F A] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι]
    [Finite ι] (b : Basis ι F B) (x : B) (i : ι) :
    (b.ofLinearDisjoint h₁ h₂).repr (algebraMap B E x) i = algebraMap F A (b.repr x i) := by
  have : Fintype ι := Fintype.ofFinite ι
  have h := ((b.ofLinearDisjoint h₁ h₂).sum_repr (algebraMap B E x)).trans
    <| RingHom.congr_arg (algebraMap B E) (b.sum_repr x).symm
  simp_rw [map_sum, Algebra.smul_def, map_mul, (ofLinearDisjoint_apply h₁ h₂ b _).symm,
    ← IsScalarTower.algebraMap_apply F B E, IsScalarTower.algebraMap_apply F A E,
    ← Algebra.smul_def] at h
  replace h := congr_arg ((↑) : (ι →₀ A) → ι → A) (congr_arg (b.ofLinearDisjoint h₁ h₂).repr h)
  rw [(b.ofLinearDisjoint h₁ h₂).repr_sum_self, (b.ofLinearDisjoint h₁ h₂).repr_sum_self] at h
  exact congr_fun h i

theorem Basis.ofLinearDisjoint_leftMulMatrix_eq {F : Type*} {E : Type*} [Field F] [Field E]
    [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F E] (h₁ : A.LinearDisjoint B)
    (h₂ : A ⊔ B = ⊤) {ι : Type*} [Nonempty ι] [Fintype ι] [DecidableEq ι] (b : Basis ι F B)
    (x : B) :
    Algebra.leftMulMatrix (Basis.ofLinearDisjoint h₁ h₂ b) (algebraMap B E x) =
      RingHom.mapMatrix (algebraMap F A) (Algebra.leftMulMatrix b x) := by
  ext
  simp [Algebra.leftMulMatrix_eq_repr_mul, ← b.ofLinearDisjoint_repr_apply h₁ h₂]

theorem IntermediateField.LinearDisjoint.trace_algebraMap_eq {F : Type*} {E : Type*} [Field F]
    [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F E]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) (x : B) :
    Algebra.trace A E (algebraMap B E x) = algebraMap F A (Algebra.trace F B x) := by
  let b := Module.Free.chooseBasis F B
  simp_rw [Algebra.trace_eq_matrix_trace b,
    Algebra.trace_eq_matrix_trace (b.ofLinearDisjoint h₁ h₂),
    Matrix.trace, map_sum, b.ofLinearDisjoint_leftMulMatrix_eq, RingHom.mapMatrix_apply,
    Matrix.diag_apply, Matrix.map_apply]

theorem IntermediateField.LinearDisjoint.norm_algebraMap_eq {F : Type*} {E : Type*} [Field F]
    [Field E] [Algebra F E] {A B : IntermediateField F E} [FiniteDimensional F E]
    (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) (x : B) :
    Algebra.norm A (algebraMap B E x) = algebraMap F A (Algebra.norm F x) := by
  let b := Module.Free.chooseBasis F B
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (b.ofLinearDisjoint h₁ h₂),
    b.ofLinearDisjoint_leftMulMatrix_eq, RingHom.map_det]

theorem LinearMap.BilinForm.dualBasis_eq_iff {V : Type*} {K : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] [Finite ι] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V) :
    B.dualBasis hB b = v ↔ ∀ i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ ↦ by rw [← h, apply_dualBasis_left],
    fun h ↦ funext fun _ ↦ (B.dualBasis hB b).ext_elem_iff.mpr fun _ ↦ by
      rw [dualBasis_repr_apply, dualBasis_repr_apply, apply_dualBasis_left, h]⟩

/-- Doc -/
noncomputable def Basis.traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι]  [DecidableEq ι]
    (b : Basis ι K L) :
    Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

@[simp]
theorem Basis.traceDual_repr_apply {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (x : L) (i : ι) :
    (b.traceDual).repr x i = (Algebra.traceForm K L x) (b i) :=
  (Algebra.traceForm K L).dualBasis_repr_apply _ b _ i

theorem Basis.apply_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
theorem Basis.traceDual_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    b.traceDual.traceDual = b :=
  (Algebra.traceForm K L).dualBasis_dualBasis _ (Algebra.traceForm_isSymm K) _

@[simp]
theorem Basis.traceDual_involutive (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  fun b ↦ traceDual_traceDual b

theorem Basis.traceDual_injective (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceDual_involutive K L).injective

@[simp]
theorem Basis.traceDual_inj {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b b' : Basis ι K L):
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

theorem Basis.traceDual_eq_iff {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (v : ι → L) :
    b.traceDual = v ↔
      ∀ i j, Algebra.traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

@[simp]
theorem Submodule.traceDual_restrictScalars (A K : Type*) {L B : Type*} [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) :
    (Submodule.traceDual A K I).restrictScalars A =
      (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

theorem Submodule.traceDual_span_of_basis (A : Type*) {K L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
  rw [traceDual_restrictScalars, hb]
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

theorem IsLocalization.map_injective_of_injective' {A : Type*} [CommRing A] {B : Type*}
    [CommRing B] {f : A →+* B} (K : Type*) {M : Submonoid A} [CommRing K] [IsDomain K] [Algebra A K]
    [NoZeroSMulDivisors A K] [IsLocalization M K] (L : Type*) {N : Submonoid B} [CommRing L]
    [IsDomain L] [Algebra B L] [NoZeroSMulDivisors B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N) (hf' : Function.Injective f) :
    Function.Injective (map L f hf : K →+* L) := by
  by_cases hM : 0 ∈ M
  · have hK : Unique K := uniqueOfZeroMem hM
    obtain ⟨x, y, h⟩ : ∃ x y : K, x ≠ y := nontrivial_iff.mp inferInstance
    simp [hK.uniq x, hK.uniq y] at h
  refine (injective_iff_map_eq_zero (map L f hf)).mpr fun x h ↦ ?_
  have h₁ : (sec M x).1 = 0 := by
    simpa [map, lift, Submonoid.LocalizationWithZeroMap.lift_apply,
      _root_.map_eq_zero_iff f hf'] using h
  have h₂ : ((sec M x).2 : A) ≠ 0 := ne_of_mem_of_not_mem (SetLike.coe_mem (sec M x).2) hM
  simpa [h₁, h₂] using sec_spec M x

theorem FractionalIdeal.extended_ne_zero {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {f : A →+* B} {K : Type*}
    {M : Submonoid A} [CommRing K] [IsDomain K] [Algebra A K] [NoZeroSMulDivisors A K]
    [IsLocalization M K] (L : Type*) [CommRing L] [IsDomain L] [Algebra B L]
    [NoZeroSMulDivisors B L] {N : Submonoid B} [IsLocalization N L] (hf : M ≤ Submonoid.comap f N)
    (hf' : Function.Injective f) {I : FractionalIdeal M K} (hI : I ≠ 0) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ hf hf')).mpr hx₂

theorem FractionalIdeal.extended_inv {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*}
    [Field K] [Algebra A K] [IsLocalization A⁰ K] {B : Type*} [CommRing B] [IsDedekindDomain B]
    {L : Type*} [Field L] [Algebra B L] [Algebra A B] [NoZeroSMulDivisors A B]
    [h : IsLocalization B⁰ L]
    {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs (f := algebraMap A B) I⁻¹ =
       (extended L hs (f := algebraMap A B) I : FractionalIdeal B⁰ L)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀, ← extended_mul, inv_mul_cancel₀ hI, extended_one]
  exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI

theorem FractionalIdeal.extended_coeIdeal_eq_map' {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {f : A →+* B} {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N) (I : Ideal A) :
    (I : FractionalIdeal M K).extended L hf = (I.map f : FractionalIdeal N L) := by
  rw [Ideal.map, Ideal.span, ← coeToSubmodule_inj, Ideal.submodule_span_eq, coe_coeIdeal,
    IsLocalization.coeSubmodule_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_ , ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

theorem FractionalIdeal.extended_coeIdeal_eq_map {A : Type*} [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsLocalization A⁰ K] {B : Type*} [CommRing B]
    [IsDedekindDomain B] (L : Type*) [Field L] [Algebra B L] [Algebra A B] [NoZeroSMulDivisors A B]
    [h : IsLocalization B⁰ L] (I : Ideal A) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    (I : FractionalIdeal A⁰ K).extended L hs =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) :=
  FractionalIdeal.extended_coeIdeal_eq_map' _ _ _

instance (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F] [Algebra F K] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) (𝓞 F)⁰) K := by
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, by simpa using ne_zero ha, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa using ne_zero hx

open nonZeroDivisors Algebra FractionalIdeal

section dual

variable {A B C K L M : Type*}
variable [CommRing A] [Field K] [Algebra A K] [IsDomain A] [IsFractionRing A K]
  [IsIntegrallyClosed A]
variable [CommRing B] [Field L] [Algebra B L] [IsDedekindDomain B] [IsFractionRing B L]
variable [CommRing C] [Field M] [Algebra C M] [IsDedekindDomain C] [IsFractionRing C M]
variable [Algebra A B] [Algebra A C] [Algebra A L] [Algebra A M]
variable [Algebra B C] [Algebra B M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsIntegralClosure B A L] [IsIntegralClosure C A M] [IsIntegralClosure C B M]
variable [IsScalarTower A K M] [IsScalarTower A C M] [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsScalarTower B L M] [IsScalarTower B C M]
variable [IsScalarTower K L M]
variable [FiniteDimensional K M] [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
variable [NoZeroSMulDivisors B C]

theorem FractionalIdeal.dual_eq_dual_mul_dual
    [IsLocalization (Algebra.algebraMapSubmonoid C B⁰) M] :
    haveI h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
        FaithfulSMul.algebraMap_injective _ _
    haveI : Module.Finite L M := Module.Finite.right K L M
    haveI : Module.Finite K L := Module.Finite.left K L M
    haveI : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
    dual A K (1 : FractionalIdeal C⁰ M) = dual B L (1 : FractionalIdeal C⁰ M) *
        (dual A K (1 : FractionalIdeal B⁰ L)).extended M h := by

  have : Module.Finite L M := Module.Finite.right K L M
  have : Module.Finite K L := Module.Finite.left K L M
  have : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M

  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <| FaithfulSMul.algebraMap_injective _ _

  have hI₁ : dual A K (1 : FractionalIdeal B⁰ L) ≠ 0 :=
    dual_ne_zero A K <| one_ne_zero' (FractionalIdeal B⁰ L)
  have hI₂ : (dual A K (1 : FractionalIdeal B⁰ L)).extended M h ≠ 0 :=
    extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI₁

  have h_loc {x : L} : algebraMap L M x = IsLocalization.map M (algebraMap B C) h x :=
    IsLocalization.algebraMap_apply_eq_map_map_submonoid B⁰ C L M x

  refine le_antisymm ?_ (fun x hx ↦ ?_)
  · intro x hx
    dsimp at hx ⊢
    rw [mem_coe] at hx ⊢
    have h₁ (c : C) : trace L M (x * algebraMap C M c) ∈
        dual A K (1 : FractionalIdeal B⁰ L) := by
      rw [mem_dual (one_ne_zero' (FractionalIdeal B⁰ L))]
      rintro _ ⟨y, _, rfl⟩
      simp
      rw [mul_comm, ← smul_eq_mul, ← map_smul, trace_trace]
      rw [mem_dual (one_ne_zero' (FractionalIdeal C⁰ M))] at hx
      simp at hx
      specialize hx (algebraMap B L y • algebraMap C M c) (by
        refine (mem_one_iff C⁰).mpr ?_
        use algebraMap B C y * c
        rw [Algebra.smul_def]
        rw [map_mul]
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
      rwa [mul_smul_comm] at hx
    have h₂ {c : C} {z : L} (hz : z ∈ (dual A K (1 : FractionalIdeal B⁰ L))⁻¹) :
        trace L M (x * algebraMap L M z * algebraMap C M c) ∈ (algebraMap B L).range := by
      rw [mem_inv_iff] at hz
      rw [mul_comm x, mul_assoc, ← smul_def, map_smul, smul_eq_mul]
      have := hz (trace L M (x * (algebraMap C M c))) (h₁ c)
      obtain ⟨b, hb₁, hb₂⟩ := this
      rw [← hb₂]
      simp
      refine dual_ne_zero A K (by simp)
    have h₃ {z : L} (hz : z ∈ (dual A K (1 : FractionalIdeal B⁰ L))⁻¹) :
        x * algebraMap L M z ∈ dual B L (1 : FractionalIdeal C⁰ M) := by
      rw [mem_dual (one_ne_zero' (FractionalIdeal C⁰ M))]
      rintro m ⟨m, _, rfl⟩
      rw [linearMap_apply, traceForm_apply]
      exact h₂ hz
    have h₄ {z : M}
        (hz : z ∈ ((dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹) :
        x * z ∈ dual B L (1 : FractionalIdeal C⁰ M) := by
      have : ((dual A K (1 : FractionalIdeal B⁰ L))⁻¹.extended M h) =
        ((dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv₀ hI₂, ← extended_mul, inv_mul_cancel₀ hI₁, extended_one]
      rw [← this, ← mem_coe, coe_extended_eq_span, Submodule.mem_span_image_iff_exists_fun] at hz
      obtain ⟨s, hs, _, rfl⟩ := hz
      simp_rw [Finset.mul_sum, mul_smul_comm]
      refine Submodule.sum_smul_mem _ _ fun i _ ↦ ?_
      rw [← h_loc]
      apply h₃
      exact hs i.prop
    have h₅ : spanSingleton C⁰ x * ((dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹ ≤
          dual B L (1 : FractionalIdeal C⁰ M) := by
      refine spanSingleton_mul_le_iff.mpr fun z hz ↦ h₄ hz
    rw [← spanSingleton_le_iff_mem]
    have h₆ := mul_right_mono ((dual A K (1 : FractionalIdeal B⁰ L)).extended M h) h₅
    dsimp at h₆
    rwa [inv_mul_cancel_right₀] at h₆
    exact hI₂
  · simp only [val_eq_coe, coe_mul, coe_dual_one, coe_extended_eq_span] at hx ⊢
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
        obtain ⟨s, hs, _, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun _).mp hn
        simp_rw [Finset.mul_sum, mul_smul_comm]
        refine Submodule.sum_smul_mem _ _ fun i _ ↦ Submodule.mem_traceDual.mpr fun c hc ↦ ?_
        obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hc
        rw [traceForm_apply, ← Algebra.trace_trace (S := L), ← h_loc, mul_comm m, mul_assoc,
          ← Algebra.smul_def, map_smul]
        apply (mem_dual (by simp)).mp (hs i.prop)
        simp only [Submodule.mem_traceDual, Submodule.mem_one, traceForm_apply, RingHom.mem_range,
          forall_exists_index, forall_apply_eq_imp_iff] at hm
  
        obtain ⟨b, hb⟩ := hm a
        rw [← hb]
        exact coe_mem_one B⁰ b
    | add x _ y _ hx hy => exact Submodule.add_mem _ hx hy

theorem FractionalIdeal.dual_eq_dual_mul_dual'
    [IsLocalization (Algebra.algebraMapSubmonoid C B⁰) M] :
    haveI h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <|
        FaithfulSMul.algebraMap_injective _ _
    haveI : Module.Finite L M := Module.Finite.right K L M
    haveI : Module.Finite K L := Module.Finite.left K L M
    haveI : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
    dual A K (1 : FractionalIdeal C⁰ M) = dual B L (1 : FractionalIdeal C⁰ M) *
        (dual A K (1 : FractionalIdeal B⁰ L)).extended M h := by

  have : Algebra.IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
  have : Module.Finite L M := Module.Finite.right K L M
  have : Module.Finite K L := Module.Finite.left K L M

  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <| FaithfulSMul.algebraMap_injective _ _


  suffices dual B L (1 : FractionalIdeal C⁰ M) = dual A K (1 : FractionalIdeal C⁰ M) *
      ((dual A K (1 : FractionalIdeal B⁰ L)).extended M h)⁻¹ by
    sorry
  ext x
  calc x ∈ dual B L 1
    _ ↔ ∀ z ∈ (1 : FractionalIdeal C⁰ M), traceForm L M x z ∈ (algebraMap B L).range := ?_
    _ ↔ ∀ z ∈ (1 : FractionalIdeal C⁰ M), ∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L),
        y * traceForm L M x z ∈ (dual A K (1 : FractionalIdeal B⁰ L)) := ?_
    _ ↔ ∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L), ∀ z ∈ (1 : FractionalIdeal C⁰ M),
        traceForm K L y (traceForm L M x z) ∈ (algebraMap A K).range := ?_
    _ ↔ ∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L), ∀ z ∈ (1 : FractionalIdeal C⁰ M),
        traceForm K M x (algebraMap L M y * z) ∈ (algebraMap A K).range := ?_
    _ ↔ ∀ y ∈ extended M h (dual A K (1 : FractionalIdeal B⁰ L)),
        x * y ∈ dual A K (1 : FractionalIdeal C⁰ M) := ?_
    _ ↔ x ∈ dual A K 1 * (extended M h (dual A K 1))⁻¹ := ?_
  · rw [mem_dual (by simp)]
  · have h₁ : ((algebraMap B L).range : Set L) = (1 : FractionalIdeal B⁰ L) := by
      sorry
    refine forall₂_congr fun z hz ↦ ⟨?_, ?_⟩
    · intro h y hy
      rw [← mem_coe, ← dual_mul_self A K (I := (1 : FractionalIdeal B⁰ L)) (by simp), coe_mul]
      exact Submodule.mul_mem_mul hy (by simpa [h₁])
    · intro h
      have := mem_div_iff_of_nonzero (I := dual A K 1) (J := dual A K 1) (R₁ := B) (K := L)
        (x := ((traceForm L M) x) z)
      simp_rw [mul_comm _ (((traceForm L M) x) z)] at h
      rw [← this] at h
      simp at h
      rwa [← SetLike.mem_coe, h₁]
      simp
  · conv_lhs =>
      enter [2, 2, y, hy]
      rw [mem_dual (by simp)]
    constructor
    · intro h y hy z hz

      sorry
    · intro h _ h' y hy z hz
      rw [mem_one_iff] at h'
      obtain ⟨c, rfl⟩ := h'
      simp_rw [traceForm_apply] at h ⊢
      specialize h y hy (algebraMap C M c * algebraMap L M z) (by
        rw [mem_one_iff] at ⊢ hz
        obtain ⟨b, rfl⟩ := hz
        use c * algebraMap B C b
        rw [map_mul]
        sorry)
      convert h using 2
      rw [mul_comm _ (algebraMap L M z), ← mul_assoc x, mul_comm _ (algebraMap L M z),
        mul_assoc _ x, ← smul_def, map_smul, smul_eq_mul]
      ring
  · refine forall₂_congr fun y hy ↦ ?_
    simp_rw [traceForm_apply, ← smul_eq_mul, ← map_smul, trace_trace, smul_eq_mul, smul_def,
      mul_comm x, mul_assoc]
  · sorry



#exit
      rw [← smul_def, ← trace_trace (S := L), map_smul] at h ⊢
      rw [mem_dual (by simp)] at hy

      rw [mem_one_iff] at hz
--      obtain ⟨c, rfl⟩ := hz
      specialize hy (trace L M z) sorry


      specialize hy (((traceForm L M) x) z) (by
        rw [mem_one_iff] at hz ⊢
        obtain ⟨c, rfl⟩ := hz
        sorry)
      exact hy


#exit

    simp_rw [traceForm_apply, ← smul_eq_mul, ← map_smul, trace_trace, smul_eq_mul, smul_def,
      mul_comm x]
    constructor
    · intro h
      specialize h 1 (one_mem_one _)
      rwa [one_mul] at h
    · intro h z hz
 --     rw [mem_one_iff] at h'
--      obtain ⟨c, rfl⟩ := h'
--      obtain ⟨a, ha⟩ := h
      rw [mem_dual (by simp)] at hy
      simp at hy
      specialize hy (trace L M z)
      rw [mul_comm _ x, ← mul_assoc, mul_comm]



      sorry
  · sorry
-- Set.forall_mem_image

#exit
    simp_rw [traceForm_apply]
    constructor
    · intro h y hy z hz
      specialize h z hz
      rw [← mem_coe, ← dual_mul_self A K (I := (1 : FractionalIdeal B⁰ L)) (by simp), coe_mul]
      refine Submodule.mul_mem_mul hy (by simpa using h)
    · intro h z hz
      specialize h 1 ?_
      sorry
      specialize h z hz
      rw [one_mul, mem_dual (by simp)] at h
      sorry
  ·

    sorry
  · rw [← Set.forall_mem_image (s := dual A K 1)]
    sorry
  · simp_rw [traceForm_apply, ← smul_eq_mul, ← map_smul, trace_trace, smul_eq_mul, mul_comm x,
      ← mul_smul_comm, ← traceForm_apply]


    sorry
  · sorry
  · sorry








#exit


  have h₁ : x ∈ dual B L (1 : FractionalIdeal C⁰ M) ↔ ∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L),
      ∀ z ∈ (1 : FractionalIdeal C⁰ M),
      traceForm K L y (traceForm L M x z) ∈ (algebraMap A K).range := by
    rw [mem_dual]
    constructor
    · intro h y hy z hz
      rw [mem_dual] at hy
      specialize h z hz
      obtain ⟨s, hs⟩ := h
      rw [← hs]
      apply hy

      sorry
    ·
      sorry
  rw [h₁]
  have h₂ : (∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L), ∀ z ∈ (1 : FractionalIdeal C⁰ M),
      trace K L (y * trace L M (x * z)) ∈ (algebraMap A K).range) ↔
      ∀ y ∈ dual A K (1 : FractionalIdeal B⁰ L),
      trace K M (x * algebraMap L M y) ∈ (algebraMap A K).range := sorry
  rw [h₂]


#exit

end dual

section numberfield

open NumberField

--Generalize
variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal :
    differentIdeal (𝓞 K) (𝓞 M) =
       differentIdeal (𝓞 L) (𝓞 M) *
        (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (𝓞 M)) := by
  rw [← FractionalIdeal.coeIdeal_inj (K := M), FractionalIdeal.coeIdeal_mul,
    coeIdeal_differentIdeal (𝓞 K) K, coeIdeal_differentIdeal (𝓞 L) L]
  have h : (𝓞 L)⁰ ≤ Submonoid.comap (algebraMap (𝓞 L) (𝓞 M)) (𝓞 M)⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ <| FaithfulSMul.algebraMap_injective _ _
  have h' : dual (𝓞 K) K (1 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 := by simp
  have : (Ideal.map (algebraMap (𝓞 L) (𝓞 M))
      (differentIdeal (𝓞 K) (𝓞 L)) : FractionalIdeal (𝓞 M)⁰ M) =
      ((FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (𝓞 L)⁰ L)).extended M h)⁻¹ := by
    rw [← extended_coeIdeal_eq_map L M]
    rw [← mul_inv_eq_one₀, inv_inv, ← extended_mul, coeIdeal_differentIdeal (𝓞 K) K,
      inv_mul_cancel₀, extended_one]
    exact h'
    rw [← FractionalIdeal.extended_inv]
    apply FractionalIdeal.extended_ne_zero
    exact RingOfIntegers.algebraMap.injective L M
    apply inv_ne_zero
    exact h'
    exact h'
  rw [this, ← mul_inv, inv_eq_iff_eq_inv, inv_inv]
  apply FractionalIdeal.dual_eq_dual_mul_dual

end numberfield

section not_clean

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] (L₁ L₂ : IntermediateField K M)
  (h : IsCoprime (Ideal.under (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L₁)))
    (Ideal.under (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L₂))))

-- theorem Submodule.traceDual_span_of_basis (A : Type*) {K L B : Type*}
--     [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
--     [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
--     [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) {ι : Type*} [Finite ι]
--     [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
--     (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
--   rw [traceDual_restrictScalars, hb]
--   exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

example (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) (I : Submodule (𝓞 L₂) L₂) {ι : Type*}
    [Finite ι] (b : Basis ι K L₂)
    (hI : I.restrictScalars (𝓞 K) = Submodule.span (𝓞 K) (Set.range b)) : 1 = 0:= by
  classical
  have : Nonempty ι := sorry
  have t₁ := I.traceDual_span_of_basis (b := b) (𝓞 K) hI
  let B := b.ofLinearDisjoint h₁ h₂
  have hI' : (Submodule.span (𝓞 M) (algebraMap L₂ M '' I)).restrictScalars (𝓞 L₁) =
    Submodule.span (𝓞 L₁) (Set.range B) := sorry
  have t₂ := (Submodule.span (𝓞 M) (algebraMap L₂ M '' I)).traceDual_span_of_basis (b := B)
    (𝓞 L₁) hI'
  have := Submodule.span (𝓞 L₁) (Set.range B.traceDual)

  sorry

example : IsCoprime ((differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)))
    ((differentIdeal (𝓞 K) (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 M))) := by
  rw [Ideal.isCoprime_iff_exists] at h ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨algebraMap (𝓞 K) (𝓞 M) x, ?_, algebraMap (𝓞 K) (𝓞 M) y, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨algebraMap (𝓞 K) (𝓞 L₁) x, hx, rfl⟩
  · apply Submodule.subset_span
    exact ⟨algebraMap (𝓞 K) (𝓞 L₂) y, hy, rfl⟩
  · rw [← map_add, hxy, map_one]

example : IsCoprime (differentIdeal (𝓞 L₁) (𝓞 M)) (differentIdeal (𝓞 L₂) (𝓞 M)) := by
  rw [Ideal.isCoprime_iff_exists] at h ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨algebraMap (𝓞 K) (𝓞 M) x, ?_, algebraMap (𝓞 K) (𝓞 M) y, ?_, ?_⟩
  · have : algebraMap (𝓞 K) M x ∈ (differentIdeal (𝓞 L₁) (𝓞 M) : FractionalIdeal (𝓞 M)⁰ M) := by
      simp at hx
      replace hx : (algebraMap (𝓞 K) L₁) y ∈
        (differentIdeal (𝓞 K) (𝓞 L₁) : FractionalIdeal (𝓞 L₁)⁰ L₁) := sorry
      rw [coeIdeal_differentIdeal (𝓞 K) K, mem_inv_iff] at hx
      rw [coeIdeal_differentIdeal (𝓞 L₁) L₁, mem_inv_iff]
      intro m hm
      simp [mem_dual] at hx hm



      sorry


    sorry
  ·
    sorry
  · rw [← map_add, hxy, map_one]

theorem useful :
    differentIdeal (𝓞 L₁) (𝓞 M) ∣ (differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)) := by
  sorry
  -- rw [Ideal.dvd_iff_le]

  -- rw [← FractionalIdeal.coeIdeal_le_coeIdeal M]
  -- rw [coeIdeal_differentIdeal (𝓞 L₁) L₁]
  -- suffices (Ideal.map (algebraMap (𝓞 L₁) (𝓞 M))
  --     (differentIdeal (𝓞 K) (𝓞 L₁)) : FractionalIdeal (𝓞 M)⁰ M) *
  --       (dual (𝓞 L₁) (L₁) 1) ≤ 1 by
  --   have := FractionalIdeal.mul_right_mono (dual (𝓞 L₁) (L₁) (1 : FractionalIdeal (𝓞 M)⁰ M))⁻¹ this
  --   simpa using this
  -- rw [mul_comm]
  -- rw [← FractionalIdeal.dual_inv]

  -- rw [FractionalIdeal.le_inv_comm]
  -- rw [← FractionalIdeal.extended_coeIdeal_eq_map (M := (𝓞 L₁)⁰) (N := (𝓞 M)⁰) (K := L₁) M]
  -- rw [← FractionalIdeal.extended_inv]
  -- rw [coeIdeal_differentIdeal (𝓞 K) K, inv_inv]
  -- have : (dual (𝓞 L₁) (L₁) (1 : FractionalIdeal (𝓞 M)⁰ M) : Submodule (𝓞 M) M) ≤
  --     (extended M sorry (M := (𝓞 L₁)⁰) (N := (𝓞 M)⁰) (K := L₁) (f := algebraMap (𝓞 L₁) (𝓞 M))
  --       (dual (𝓞 K) K (1 : FractionalIdeal (𝓞 L₁)⁰ L₁)) : Submodule (𝓞 M) M) := by
  --   simp
  --   intro x hx
  --   rw [Submodule.mem_traceDual] at hx
  --   refine Submodule.subset_span ?_
  --   refine ⟨?_, ?_, ?_⟩


  -- exact this

-- That's true only on `ℚ` because of the norm, and in fact probably not
example : (differentIdeal (𝓞 K) (𝓞 L₁)).map (algebraMap (𝓞 L₁) (𝓞 M)) =
    differentIdeal (𝓞 L₂) (𝓞 M) := by
  have main := (differentIdeal_eq_differentIdeal_mul_differentIdeal K L₁ M).symm.trans
    (differentIdeal_eq_differentIdeal_mul_differentIdeal K L₂ M)
  apply dvd_antisymm'
  · have h' : IsCoprime (differentIdeal (𝓞 L₂) (𝓞 M)) (differentIdeal (𝓞 L₁) (𝓞 M)) := by
      have t₁ := useful L₁
      have t₂ := useful L₂
      refine IsCoprime.of_isCoprime_of_dvd_left ?_ t₂
      refine IsCoprime.of_isCoprime_of_dvd_right ?_ t₁
      exact h.symm
    have := dvd_of_mul_right_eq _ main.symm
    exact h'.dvd_of_dvd_mul_left (dvd_of_mul_right_eq _ main.symm)
  · exact h.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ main)

end not_clean

open Submodule

-- example : (algebraMap (𝓞 E) (𝓞 K)).range ⊔ (algebraMap (𝓞 F) (𝓞 K)).range = ⊤ := by
--   classical
--   have main := (1 : FractionalIdeal (𝓞 K)⁰ K).dual_dual (𝓞 E) E
--   have h₁ : (1 : FractionalIdeal (𝓞 K)⁰ K).dual (𝓞 E) E =
--     span (𝓞 K) (algebraMap F K '' ((1 : FractionalIdeal (𝓞 F)⁰ F).dual ℤ ℚ)) := sorry
--   rw [← coeToSubmodule_inj, coe_dual, h₁, coe_one] at main
--   have : ((1 : FractionalIdeal (𝓞 F)⁰ F).dual ℤ ℚ : Set F) =
--     Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := sorry
--   rw [this] at main
--   let b := NumberField.integralBasis F
--   have h₂ := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) b sorry
--   have h₃ : (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) : Set F) =
--       span ℤ (Set.range ⇑b.traceDual) := sorry
--   rw [h₃] at main
--   have : (algebraMap F K : F → K) = (algebraMap F K).toIntAlgHom.toLinearMap := rfl
--   rw [this] at main
--   rw [← map_coe] at main
--   rw [map_span] at main
--   rw [← Set.range_comp] at main
--   let b₀ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) → K := fun i ↦ algebraMap F K (b i)
--   rw [span_span_of_tower] at main
--   let B : Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) E K := by

--     sorry
--   have h₆ : Set.range ((algebraMap F K).toIntAlgHom.toLinearMap ∘ b.traceDual) =
--       Set.range B.traceDual := by

--   rw [h₆] at main
--   have := Submodule.traceDual_span_of_basis (A := 𝓞 E) (B := 𝓞 K) (K := E) (L := K)
--     (I := span (𝓞 K) (Set.range B.traceDual)) (b := B.traceDual) sorry
--   rw [← restrictScalars_inj (𝓞 E), this] at main
--   simp at main

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] (L₁ L₂ : IntermediateField K M)
  (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
  {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι] (b : Basis ι K L₂)
  (hmain : (differentIdeal (𝓞 K) (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 M)) =
    differentIdeal (𝓞 L₁) (𝓞 M))
  (hb : span (𝓞 K) (Set.range b) = (1 : Submodule (𝓞 L₂) L₂).restrictScalars (𝓞 K))

include hmain in -- Is only inclusion good enough?
theorem aux₁ : span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K)) =
    (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ := by
  rw [← FractionalIdeal.coeIdeal_inj (R := (𝓞 M)) (K := M)] at hmain
  rw [coeIdeal_differentIdeal (𝓞 L₁) L₁, ← inv_eq_iff_eq_inv] at hmain
  rw [← coeToSubmodule_inj] at hmain
  rw [← hmain]
  rw [← extended_coeIdeal_eq_map L₂ M (differentIdeal (𝓞 K) (𝓞 L₂))]
  rw [← extended_inv (by simp [coeIdeal_differentIdeal (𝓞 K) K]),
    coeIdeal_differentIdeal (𝓞 K) K, inv_inv]
  rw [coe_extended_eq_span]
  congr!
  ext x
  exact IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := (𝓞 L₂)) (𝓞 L₂)⁰ (𝓞 M)
    L₂ M x

example : span (𝓞 L₁) (Set.range (b.ofLinearDisjoint h₁ h₂)) =
    (1 : Submodule (𝓞 M) M).restrictScalars (𝓞 L₁) :=  by
  have : IsScalarTower (𝓞 K) L₂ M := sorry
  have h := (1 : FractionalIdeal (𝓞 M)⁰ M).dual_dual (𝓞 L₁) L₁
  rw [← coeToSubmodule_inj, ← restrictScalars_inj (𝓞 L₁), coe_one] at h
  rw [← h, coe_dual _ _ (dual_ne_zero (𝓞 L₁) L₁ (one_ne_zero' (FractionalIdeal (𝓞 M)⁰ M)))]
  rw [← aux₁]

  have := Submodule.traceDual_span_of_basis (𝓞 K) (1 : Submodule (𝓞 L₂) L₂) b hb.symm


  have t₁ : (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ =
      span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K)) := by

    sorry
  rw [t₁]
  have t₂ : ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K : Set L₂) =
      Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L₂) L₂) := sorry
  rw [t₂]
  have := Submodule.traceDual_span_of_basis (𝓞 K) (1 : Submodule (𝓞 L₂) L₂) b hb.symm
  rw [SetLike.ext'_iff] at this
  erw [this]
  have : (algebraMap L₂ M : L₂ → M) = (IsScalarTower.toAlgHom (𝓞 K) L₂ M).toLinearMap := rfl
  rw [this, ← map_coe, map_span, ← Set.range_comp]
  rw [span_span_of_tower]
  let B := b.ofLinearDisjoint h₁ h₂
  have t₄ : Set.range ((IsScalarTower.toAlgHom (𝓞 K) L₂ M).toLinearMap ∘ b.traceDual) =
      Set.range B.traceDual := by
    refine congr_arg (Set.range ·) ?_
    rw [eq_comm, Basis.traceDual_eq_iff]
    intro i j
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe,
      Basis.ofLinearDisjoint_apply, traceForm_apply, B, IsScalarTower.coe_toAlgHom']
    rw [← map_mul, h₁.trace_algebraMap_eq]
    have :=  b.apply_traceDual i j
    rw [this]
    simp
    exact h₂
  rw [t₄]
  -- Here things get wrong...
  have t₅ := Submodule.traceDual_span_of_basis (A := 𝓞 L₁) (B := 𝓞 M) (K := L₁) (L := M)
    (I := span (𝓞 M) (Set.range B.traceDual)) (b := B.traceDual) ?_
  · rw [t₅]
    simp
    rfl
  ext
  simp [B] -- not true!
  sorry

--  have t₃ : Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L₂) L₂) ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual (𝓞 K) K : Set L₂)

example : span (𝓞 L₁) (Set.range (b.ofLinearDisjoint h₁ h₂)) =
    (1 : Submodule (𝓞 M) M).restrictScalars (𝓞 L₁) :=  by
  have h := (1 : FractionalIdeal (𝓞 M)⁰ M).dual_dual (𝓞 L₁) L₁
  rw [← coeToSubmodule_inj, ← restrictScalars_inj (𝓞 L₁), coe_one] at h
  rw [← h, coe_dual _ _ (dual_ne_zero (𝓞 L₁) L₁ (one_ne_zero' (FractionalIdeal (𝓞 M)⁰ M)))]

  have t₁ : (1 : FractionalIdeal (𝓞 M)⁰ M).dual (𝓞 L₁) L₁ =
      span (𝓞 M) (algebraMap L₂ M '' ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual ℤ ℚ)) := by
    simp

    sorry
  rw [ t₁]
  have t₂ : ((1 : FractionalIdeal (𝓞 L₂)⁰ L₂).dual ℤ ℚ : Set L₂) =
      Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L₂) L₂) := sorry
  rw [t₂]
  have t₃ : (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L₂) L₂) : Set L₂) =
      span ℤ (Set.range ⇑b.traceDual) := by
    -- have := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 L₂) L₂) b hb.symm
    -- rw [← this]
    -- ext


    sorry
  rw [t₃]
  have : (algebraMap L₂ M : L₂ → M) = (algebraMap L₂ M).toIntAlgHom.toLinearMap := rfl
  rw [this, ← map_coe, map_span, ← Set.range_comp]
  rw [span_span_of_tower]
  let B := b.ofLinearDisjoint h₁ h₂
  have t₄ : Set.range ((algebraMap L₂ M).toIntAlgHom.toLinearMap ∘ b.traceDual) =
      Set.range B.traceDual := by
    refine congr_arg (Set.range ·) ?_
    rw [eq_comm, Basis.traceDual_eq_iff]
    intro i j
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe,
      Basis.ofLinearDisjoint_apply, traceForm_apply, B]
    rw [← map_mul, h₁.trace_algebraMap_eq]
    have :=  b.apply_traceDual i j
    rw [this]
    simp
    exact h₂
  rw [t₄]
  have t₅ := Submodule.traceDual_span_of_basis (A := 𝓞 L₁) (B := 𝓞 M) (K := L₁) (L := M)
    (I := span (𝓞 M) (Set.range B.traceDual)) (b := B.traceDual)
  rw [t₅]
  simp
  rfl
  ext
  simp






#exit

  let I := ((1 : FractionalIdeal (𝓞 E)⁰ E).dual (𝓞 ℚ) ℚ).extended K
    (M := (𝓞 E)⁰) (N := (𝓞 K)⁰) (f := algebraMap (𝓞 E) (𝓞 K)) sorry


  have : (1 : FractionalIdeal (𝓞 K)⁰ K).dual (𝓞 E) E  =
      ((differentIdeal (𝓞 ℚ) (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)))⁻¹ := sorry

  have main := dual_dual (𝓞 E) E (1 : FractionalIdeal (𝓞 K)⁰ K)
  rw [← coeToSubmodule_inj, ← Submodule.restrictScalars_inj (𝓞 ℚ)] at main
  rw [coe_dual, coe_dual] at main

#exit
  have : dual (𝓞 E) E (1 : FractionalIdeal (𝓞 K)⁰ K) =
    (differentIdeal (𝓞 E) (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := sorry
  rw [this] at main
  have h₁ : differentIdeal (𝓞 E) (𝓞 K) =
    ((differentIdeal (𝓞 ℚ) (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K))) := sorry
  rw [← coeIdeal_inj (K := K)] at h₁
  rw [h₁] at main
  rw [← extended_coeIdeal_eq_map (L := K) (M := (𝓞 E)⁰) (K := E)] at main
  erw [← extended_inv, coeIdeal_differentIdeal (𝓞 ℚ) ℚ, inv_inv] at main
  let B := dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)
  let B' := B.extended K (M := (𝓞 E)⁰) (N := (𝓞 K)⁰) (f := algebraMap (𝓞 E) (𝓞 K)) sorry
  let A := dual (𝓞 F) F B'
  let O := (algebraMap (𝓞 E) K).range
  have : (A : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) ((algebraMap (𝓞 E) K).range ⊔ (algebraMap (𝓞 F) K).range) := by





end compositum
