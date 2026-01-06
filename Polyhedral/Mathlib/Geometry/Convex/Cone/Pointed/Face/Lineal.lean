-- import Mathlib.Algebra.Module.Submodule.Pointwise
-- import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

-- variable {R M N : Type*}

-- namespace PointedCone

-- open Module Pointwise

-- section Ring

-- variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- /-- The lineality space of a cone `C`, namely the submodule with carrier `C ⊓ -C`. -/
-- def lineal (C : PointedCone R M) : Submodule R M where
--   carrier := C ⊓ -C
--   add_mem' hx hy := by simpa using ⟨C.add_mem hx.1 hy.1, C.add_mem hy.2 hx.2⟩
--   zero_mem' := by simp
--   smul_mem' r _ hx := by
--     by_cases hr : 0 ≤ r
--     · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
--     · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
--       simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

-- @[simp]
-- lemma lineal_eq_inter_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by rfl

-- lemma mem_lineal {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by rfl

-- @[simp]
-- lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp

-- -- -- this should go to submodule.
-- -- variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]
-- -- in
-- -- @[simp]
-- -- lemma restrictScalars_sSup {s : Set (Submodule R M)} :
-- --     (sSup s).restrictScalars S = sSup (Submodule.restrictScalars S '' s) :=
-- --   (Submodule.restrictScalarsLatticeHom S R M).map_sSup' s

-- /- The lineality space of a cone is the supremum of its submodules. -/
-- theorem lineal_eq_sSup (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C} := by
--   rw [le_antisymm_iff]
--   refine ⟨le_sSup (lineal_le C), ?_⟩
--   intro x hx
--   have hC : sSup {S : Submodule R M | S ≤ C} ≤ C := by simp
--   exact mem_lineal.mpr ⟨hC hx, hC (neg_mem hx : -x ∈ _)⟩

-- end Ring

-- namespace IsFaceOf

-- section Ring

-- variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
-- variable {C F : PointedCone R M}

-- lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
--   fun _ hx => hF.mem_of_add_mem hx.1 hx.2 (by simp)

-- lemma lineal_eq (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
--   ext
--   constructor <;> intro ⟨hx, hx'⟩
--   · exact ⟨hF.le hx, hF.le hx'⟩
--   constructor
--   · exact hF.mem_of_add_mem hx hx' (by simp)
--   · exact hF.mem_of_add_mem hx' hx (by simp)

-- end Ring

-- section Field

-- variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
-- variable {C F : PointedCone R M}

-- /-- The lineality space of a cone is a face. -/
-- lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
--   rw [iff_mem_of_add_mem]
--   simp only [PointedCone.lineal_le, true_and]
--   intro _ _ xc yc xyf
--   simp [neg_add_rev, xc, true_and] at xyf ⊢
--   simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

-- end Field

-- end IsFaceOf

-- end PointedCone
