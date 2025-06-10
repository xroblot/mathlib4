/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Prod.Lex

/-!

-/

namespace Prod.Lex

variable (α β : Type*)

def prodUnique [PartialOrder α] [Preorder β] [Unique β] : α ×ₗ β ≃o α where
  toFun x := (ofLex x).1
  invFun x := toLex (x, Inhabited.default)
  left_inv x := x.rec fun | (a, b) => (by simpa using Unique.default_eq b)
  right_inv x := by simp
  map_rel_iff' {a b} := by
    induction a using _root_.Lex.rec with | h a
    induction b using _root_.Lex.rec with | h b
    rw [Prod.Lex.toLex_le_toLex]
    have : a.2 ≤ b.2 := (Subsingleton.allEq _ _).le
    simpa [this] using le_iff_lt_or_eq

variable {α β} in
@[simp]
theorem prodUnique_apply [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β) :
    prodUnique α β x = (ofLex x).1 := rfl

def uniqueProd [Preorder α] [Unique α] [LE β] :  α ×ₗ β ≃o β where
  toFun x := (ofLex x).2
  invFun x := toLex (Inhabited.default, x)
  left_inv x := x.rec fun | (a, b) => (by simpa using Unique.default_eq a)
  right_inv x := by simp
  map_rel_iff' {a b} := by
    induction a using _root_.Lex.rec with | h a
    induction b using _root_.Lex.rec with | h b
    rw [Prod.Lex.toLex_le_toLex]
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    have hlt : ¬ a.1 < b.1 := not_lt_of_subsingleton
    simp [heq, hlt]

end Prod.Lex
