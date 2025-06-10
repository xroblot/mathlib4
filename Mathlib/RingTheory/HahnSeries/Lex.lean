/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.Hom.Lex
import Mathlib.Order.PiLex
import Mathlib.RingTheory.HahnSeries.Addition

/-!

# Lexicographical order on Hahn series

In this file, we define lexicographical ordered `Lex (HahnSeries Γ R)`, and show this
is a `LinearOrder` when `Γ` and `R` themselves are linearly ordered. Additionally,
it is an ordered group when `R` is.

-/

namespace HahnSeries

section PartialOrder

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [Zero R] [PartialOrder R]

variable (Γ R) in
instance instPartialOrder : PartialOrder (Lex (HahnSeries Γ R)) :=
  PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y ↦ by simp

theorem lt_iff (a b : Lex (HahnSeries Γ R)) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → (ofLex a).coeff j = (ofLex b).coeff j)
    ∧ (ofLex a).coeff i < (ofLex b).coeff i := by rfl

end PartialOrder

section LinearOrder

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [Zero R] [LinearOrder R]

variable (Γ R) in
noncomputable
instance instLinearOrder : LinearOrder (Lex (HahnSeries Γ R)) where
  le_total := by
    intro a b
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
    · have hab := Function.ne_iff.mp <| HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i ≠ 0} ∪ {i : Γ | (ofLex b).coeff i ≠ 0}
      let v := {i : Γ | (ofLex a).coeff i ≠ (ofLex b).coeff i}
      have hvu : v ⊆ u := by
        intro i h
        rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        contrapose! h
        rw [Set.notMem_setOf_iff, Mathlib.Tactic.PushNeg.not_ne_eq, h.1, h.2]
      have hv : v.IsWF :=
        ((ofLex a).isPWO_support'.isWF.union (ofLex b).isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i → (ofLex a).coeff j = (ofLex b).coeff j :=
        not_imp_not.mp <| fun h' ↦ hv.not_lt_min hab h'
      have hne : (ofLex a).coeff i ≠ (ofLex b).coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj ↦ (hji j hj).symm, hi⟩)

  toDecidableLE := Classical.decRel _

theorem leadingCoeff_pos_iff {x : Lex (HahnSeries Γ R)} : 0 < (ofLex x).leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) ≠ 0 := leadingCoeff_ne_iff.mp hpos.ne.symm
    have htop : (ofLex x).orderTop ≠ ⊤ := ne_zero_iff_orderTop.mp hne
    use (ofLex x).orderTop.untop htop
    constructor
    · intro j hj
      simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
    · rw [coeff_untop_eq_leadingCoeff hne]
      simpa using hpos
  · intro ⟨i, hj, hi⟩
    have horder : (ofLex x).orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : (ofLex x).orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : ofLex x ≠ 0 := ne_zero_iff_orderTop.mpr htop
    have horder' : (ofLex x).orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [← coeff_untop_eq_leadingCoeff hne, horder']
    simpa using hi

theorem leadingCoeff_nonneg_iff {x : Lex (HahnSeries Γ R)} :
    0 ≤ (ofLex x).leadingCoeff ↔ 0 ≤ x := by
  constructor
  · intro h
    obtain heq | hlt := eq_or_lt_of_le h
    · exact le_of_eq (leadingCoeff_eq_iff.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · intro h
    obtain rfl | hlt := eq_or_lt_of_le h
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

theorem leadingCoeff_neg_iff {x : Lex (HahnSeries Γ R)} : (ofLex x).leadingCoeff < 0 ↔ x < 0 := by
  simpa using (leadingCoeff_nonneg_iff (x := x)).not

theorem leadingCoeff_nonpos_iff {x : Lex (HahnSeries Γ R)} :
    (ofLex x).leadingCoeff ≤ 0 ↔ x ≤ 0 := by
  simpa using (leadingCoeff_pos_iff (x := x)).not

end LinearOrder

section OrderedGroup

variable {Γ : Type*} {R : Type*}
variable [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

variable (Γ) in
instance instIsOrderedAddMonoid (R : Type*) [PartialOrder R] [AddCommGroup R]
    [IsOrderedAddMonoid R] : IsOrderedAddMonoid (Lex (HahnSeries Γ R)) where
  add_le_add_left := by
    intro a b hab c
    obtain rfl | hlt := eq_or_lt_of_le hab
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hi⟩ := hlt
      use i
      aesop

theorem support_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).support = (ofLex x).support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

theorem orderTop_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).orderTop = (ofLex x).orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

theorem order_abs [Zero Γ] (x : Lex (HahnSeries Γ R)) : (ofLex |x|).order = (ofLex x).order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x ≠ 0 := hne
    have habs : ofLex |x| ≠ 0 := by
      show |x| ≠ 0
      simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne habs, order_eq_orderTop_of_ne hne']
    apply orderTop_abs

theorem leadingCoeff_abs (x : Lex (HahnSeries Γ R)) :
    (ofLex |x|).leadingCoeff = |(ofLex x).leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le, ofLex_neg, leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]

theorem abs_lt_of_orderTop_gt {x y : Lex (HahnSeries Γ R)}
    (h : (ofLex y).orderTop < (ofLex x).orderTop) : |x| < |y| := by
  refine (lt_iff _ _).mpr ⟨(ofLex y).orderTop.untop (ne_top_of_lt h), ?_⟩
  constructor
  · intro j hj
    trans 0
    · have h' : (ofLex |y|).orderTop < (ofLex |x|).orderTop := by
        simpa [orderTop_abs] using h
      refine coeff_eq_zero_of_lt_orderTop (lt_trans ?_ h')
      rw [orderTop_abs]
      exact (WithTop.lt_untop_iff _).mp hj
    · refine (coeff_eq_zero_of_lt_orderTop ?_).symm
      rw [orderTop_abs]
      exact (WithTop.lt_untop_iff _).mp hj
  · rw [HahnSeries.coeff_eq_zero_of_lt_orderTop ?_]
    · have hy0 : y ≠ 0 := HahnSeries.ne_zero_iff_orderTop.mpr <| ne_top_of_lt h
      have hy0' : ofLex |y| ≠ 0 := by
        show |y| ≠ 0
        simpa using hy0
      conv in (ofLex y).orderTop => rw [← orderTop_abs]
      rw [coeff_untop_eq_leadingCoeff hy0', leadingCoeff_pos_iff, abs_pos]
      exact hy0
    · rw [orderTop_abs]
      simpa using h

theorem achemedeanClass_le_iff {x y : Lex (HahnSeries Γ R)}:
    ArchimedeanClass.mk x ≤ ArchimedeanClass.mk y ↔
    (ofLex x).orderTop < (ofLex y).orderTop ∨ ((ofLex x).orderTop = (ofLex y).orderTop ∧
    ArchimedeanClass.mk (ofLex x).leadingCoeff ≤ ArchimedeanClass.mk (ofLex y).leadingCoeff) := by
  simp_rw [ArchimedeanClass.mk_le_mk]

  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when x's order is less than y's, this reduces to abs_lt_of_orderTop_gt
    simp only [hlt, true_or, iff_true]
    exact ⟨1, by simpa using (abs_lt_of_orderTop_gt hlt).le⟩
  · -- when x and y have the same order, this reduces to comparing their leadingCoeff
    obtain hx | hx := eq_or_ne x 0
    · -- special case: both x and y are zero
      have hy : y = 0 := by
        show ofLex y = 0
        apply orderTop_eq_top_iff.mp
        rw [← heq]
        exact orderTop_eq_top_iff.mpr hx
      simp [hx, hy]
    · -- general case: x and y are not zero
      have hx' : ofLex x ≠ 0 := hx
      have hy' : ofLex y ≠ 0 := ne_zero_iff_orderTop.mpr <| heq.symm ▸ ne_zero_iff_orderTop.mp hx'
      have hy : y ≠ 0 := hy'
      have hxabs : ofLex |x| ≠ 0 := by
        show |x| ≠ 0
        simpa using hx
      have hyabs : ofLex |y| ≠ 0 := by
        show |y| ≠ 0
        simpa using hy
      have heq' : (ofLex |x|).orderTop = (ofLex |y|).orderTop := by simpa [orderTop_abs] using heq
      constructor
      · -- x ⩿ y → x.leadingCoeff ⩿ y.leadingCoeff (⩿ is ArchimedeanOrder)
        intro ⟨n, hn⟩
        refine .inr ⟨heq, n + 1, ?_⟩
        have hn' : |y| < (n + 1) • |x| := by
          refine lt_of_le_of_lt hn <| nsmul_lt_nsmul_left ?_ (by simp)
          simpa using hx
        obtain ⟨j, hj, hi⟩ := (lt_iff _ _).mp hn'
        simp_rw [ofLex_smul, coeff_smul] at hj hi
        simp_rw [← leadingCoeff_abs]
        rw [← coeff_untop_eq_leadingCoeff hyabs, ← coeff_untop_eq_leadingCoeff hxabs]
        simp_rw [← heq']
        obtain hjlt | hjeq | hjgt := lt_trichotomy (WithTop.some j) (ofLex |x|).orderTop
        · -- impossible case: x and y differ before their leading coefficients
          have hjlt' : WithTop.some j < (ofLex |y|).orderTop := heq'.symm ▸ hjlt
          rw [coeff_eq_zero_of_lt_orderTop hjlt] at hi
          rw [coeff_eq_zero_of_lt_orderTop hjlt'] at hi
          simp at hi
        · convert hi.le <;> exact (WithTop.untop_eq_iff _).mpr hjeq.symm
        · exact (hj _ ((WithTop.untop_lt_iff _).mpr hjgt)).le
      · -- x.leadingCoeff ⩿ y.leadingCoeff → x ⩿ y
        intro h
        obtain h | ⟨_, n, hn⟩ := h
        · exact False.elim <| (lt_self_iff_false _).mp <| heq.symm.trans_gt h
        · refine ⟨n + 1, le_of_lt <| (lt_iff _ _).mpr ?_⟩
          refine ⟨(ofLex x).orderTop.untop (ne_zero_iff_orderTop.mp hx'), ?_, ?_⟩
          · -- all coefficients before the leading coefficient are zero
            intro j hj
            trans 0
            · apply coeff_eq_zero_of_lt_orderTop
              rw [orderTop_abs, ← heq]
              exact (WithTop.lt_untop_iff _).mp hj
            · suffices (ofLex |x|).coeff j = 0 by
                simp [this]
              apply coeff_eq_zero_of_lt_orderTop
              rw [orderTop_abs]
              exact (WithTop.lt_untop_iff _).mp hj
          · -- the leading coefficient determins the relation
            rw [ofLex_smul, coeff_smul]
            suffices |(ofLex y).leadingCoeff| < (n + 1) • |(ofLex x).leadingCoeff| by
              simp_rw [← leadingCoeff_abs] at this
              rw [← coeff_untop_eq_leadingCoeff hyabs, ← coeff_untop_eq_leadingCoeff hxabs] at this
              convert this using 3
              · rw [heq]
                rw [orderTop_abs]
              · simp_rw [orderTop_abs]
            refine lt_of_le_of_lt hn <| nsmul_lt_nsmul_left ?_ (by simp)
            rw [abs_pos, leadingCoeff_ne_iff]
            exact hx'
  · -- when x's order is greater than y's, neither side is true
    constructor
    · intro ⟨n, hn⟩
      contrapose! hn
      rw [← abs_nsmul]
      have hgt' : (ofLex y).orderTop < (ofLex (n • x)).orderTop := by
        rw [ofLex_smul]
        apply lt_of_lt_of_le hgt
        simpa using orderTop_smul_not_lt n (ofLex x)
      exact abs_lt_of_orderTop_gt hgt'
    · intro h
      obtain h | ⟨h, _⟩ := h <;> refine
        False.elim <| (lt_self_iff_false (ofLex y).orderTop).mp <| ?_
      · exact hgt.trans h
      · exact hgt.trans_eq h

theorem achemedeanClass_eq_iff {x y : Lex (HahnSeries Γ R)}:
    ArchimedeanClass.mk x = ArchimedeanClass.mk y ↔
    (ofLex x).orderTop = (ofLex y).orderTop ∧
    ArchimedeanClass.mk (ofLex x).leadingCoeff = ArchimedeanClass.mk (ofLex y).leadingCoeff := by

  rw [le_antisymm_iff, achemedeanClass_le_iff, achemedeanClass_le_iff]
  constructor
  · intro h
    obtain ⟨hx1 | ⟨hx1, hx2⟩, hy1 | ⟨hy1, hy2⟩⟩ := h
    · exact False.elim <| (lt_self_iff_false _).mp <| hx1.trans hy1
    · exact False.elim <| (lt_self_iff_false _).mp <| hx1.trans_eq hy1
    · exact False.elim <| (lt_self_iff_false _).mp <| hx1.trans_lt hy1
    · exact ⟨hx1, hx2.antisymm hy2⟩
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.symm, hcoeff.ge⟩⟩

variable (Γ R) in
/-- Non-top archimedean classes of `Lex (HahnSeries Γ R)` decompose into lexicographical pairs
of `order` and the non-top archimedean class of `leadingCoeff`. -/
private noncomputable
def archimedeanClassOrderHom :
    ArchimedeanClass₀ (Lex (HahnSeries Γ R)) →o Γ ×ₗ ArchimedeanClass₀ R :=
  ArchimedeanClass₀.lift_orderHom
    (fun ⟨x, hx⟩ ↦ toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne (show ofLex x ≠ 0 by exact hx)]),
      ArchimedeanClass₀.mk (show (ofLex x).leadingCoeff ≠ 0 by exact leadingCoeff_ne_iff.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [Prod.Lex.le_iff]
      simp only [ofLex_toLex]
      rw [ArchimedeanClass₀.mk_le_mk] at ⊢ h
      rw [WithTop.untop_eq_iff, WithTop.untop_lt_iff]
      simpa using achemedeanClass_le_iff.mp h

variable (Γ R) in
/-- The inverse of `archimedeanClassOrderHom`. -/
private noncomputable
def archimedeanClassOrderHomInv :
    Γ ×ₗ ArchimedeanClass₀ R →o ArchimedeanClass₀ (Lex (HahnSeries Γ R)) where
  toFun x := (ofLex x).2.lift_orderHom
    (fun a ↦ ArchimedeanClass₀.mk (show toLex (single (ofLex x).1 a.val) ≠ 0 by
      show single (ofLex x).1 a.val ≠ 0
      simpa using a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [ArchimedeanClass₀.mk_le_mk] at ⊢ h
      rw [achemedeanClass_le_iff]
      simp only [ofLex_toLex, leadingCoeff_of_single]
      rw [orderTop_single ha, orderTop_single hb]
      simpa using h
  monotone' := by
    intro a b h
    induction a using Lex.rec with | h a
    induction b using Lex.rec with | h b
    obtain ⟨ao, ac⟩ := a
    obtain ⟨bo, bc⟩ := b
    obtain h | ⟨heq, hle⟩ := Prod.Lex.le_iff.mp h
    · induction ac using ArchimedeanClass₀.ind with | mk a ha
      induction bc using ArchimedeanClass₀.ind with | mk b hb
      simp only [ofLex_toLex, ArchimedeanClass₀.lift_orderHom_mk]
      rw [ArchimedeanClass₀.mk_le_mk, achemedeanClass_le_iff]
      simp only [ofLex_toLex, leadingCoeff_of_single]
      rw [orderTop_single ha, orderTop_single hb]
      exact .inl (by simpa using h)
    · rw [show ao = bo by exact heq]
      exact OrderHom.monotone _ hle

variable (Γ R) in
/-- The correspondence between non-top archimedean classes of `Lex (HahnSeries Γ R)`
and lexicographical pairs of `order` and the non-top archimedean class of `leadingCoeff`. -/
noncomputable
def archimedeanClass₀_orderIso :
    ArchimedeanClass₀ (Lex (HahnSeries Γ R)) ≃o Γ ×ₗ ArchimedeanClass₀ R := by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom Γ R) (archimedeanClassOrderHomInv Γ R)
  · ext x
    induction x using Lex.rec with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using ArchimedeanClass₀.ind with | mk a ha
    unfold archimedeanClassOrderHom archimedeanClassOrderHomInv
    simp [ha]
  · ext x
    induction x using ArchimedeanClass₀.ind with | mk a ha
    unfold archimedeanClassOrderHom archimedeanClassOrderHomInv
    suffices ArchimedeanClass.mk
        (toLex (single ((ofLex a).orderTop.untop _) (ofLex a).leadingCoeff)) =
        ArchimedeanClass.mk a by
      simpa using this
    rw [achemedeanClass_eq_iff]
    have h : (ofLex a).leadingCoeff ≠ 0 := leadingCoeff_ne_iff.mpr ha
    simp [h]

@[simp]
theorem archimedeanClass₀_orderIso_apply_fst {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    WithTop.some (ofLex (archimedeanClass₀_orderIso Γ R (ArchimedeanClass₀.mk h))).1 =
    (ofLex x).orderTop := by
  simp [archimedeanClass₀_orderIso, archimedeanClassOrderHom]

@[simp]
theorem archimedeanClass₀_orderIso_apply_snd {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    (ofLex (archimedeanClass₀_orderIso Γ R (ArchimedeanClass₀.mk h))).2.val =
    ArchimedeanClass.mk (ofLex x).leadingCoeff := by
  simp [archimedeanClass₀_orderIso, archimedeanClassOrderHom]

section Archimedean

variable [Archimedean R] [Nontrivial R]

variable (Γ R) in
/-- For `Archimedean` `R`, there is a correspondence between non-top
archimedean classes and `order`. -/
noncomputable
def archimedeanClass₀_orderIso_of_archimedean : ArchimedeanClass₀ (Lex (HahnSeries Γ R)) ≃o Γ :=
  have : Unique (ArchimedeanClass₀ R) := (nonempty_unique _).some
  (archimedeanClass₀_orderIso Γ R).trans (Prod.Lex.prodUnique _ _)

theorem archimedeanClass₀_orderIso_of_archimedean_apply {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    WithTop.some (archimedeanClass₀_orderIso_of_archimedean Γ R (ArchimedeanClass₀.mk h)) =
    (ofLex x).orderTop := by
  simp [archimedeanClass₀_orderIso_of_archimedean]

variable (Γ R) in
/-- For `Archimedean` `R`, there is a correspondence between
archimedean classes (with top) and `orderTop`. -/
noncomputable
def archimedeanClass_orderIso : ArchimedeanClass (Lex (HahnSeries Γ R)) ≃o WithTop Γ :=
  (ArchimedeanClass₀.withTop_orderIso _).symm.trans
  (OrderIso.withTopCongr (archimedeanClass₀_orderIso_of_archimedean _ _))

@[simp]
theorem archimedeanClass_orderIso_apply (x : Lex (HahnSeries Γ R)) :
    (archimedeanClass_orderIso Γ R) (ArchimedeanClass.mk x) = (ofLex x).orderTop := by
  unfold archimedeanClass_orderIso
  obtain rfl | h := eq_or_ne x 0
  · simp
  · rw [OrderIso.trans_apply, ArchimedeanClass₀.withTop_orderIso_symm_apply h]
    rw [OrderIso.withTopCongr_apply_some, archimedeanClass₀_orderIso_of_archimedean_apply h]

end Archimedean

end OrderedGroup

end HahnSeries
