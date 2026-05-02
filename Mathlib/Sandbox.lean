module

public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

theorem Subgroup.mapSubgroup_normal_iff_aux {G H : Type*} [Group G] [Group H] (f : G ≃* H)
    (L : Subgroup G) (h : (f.mapSubgroup L).Normal) : L.Normal := by
  rw [MulEquiv.mapSubgroup_apply] at h
  exact Subgroup.Normal.of_map_injective f.injective h

theorem Subgroup.mapSubgroup_normal_iff {G H : Type*} [Group G] [Group H] {f : G ≃* H}
    {L : Subgroup G} : (f.mapSubgroup L).Normal ↔ L.Normal := by
  refine ⟨fun h ↦ mapSubgroup_normal_iff_aux f L h, fun h ↦ ?_⟩
  refine mapSubgroup_normal_iff_aux f.symm (f.mapSubgroup L) ?_
  rwa [← MulEquiv.symm_mapSubgroup, OrderIso.symm_apply_apply]
