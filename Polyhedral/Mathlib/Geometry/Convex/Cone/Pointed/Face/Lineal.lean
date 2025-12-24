
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

--import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic_PR
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Face.Lattice

variable {R M N : Type*}

namespace PointedCone

open Module

section Ring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The lineality space of a cone. -/
def lineal (C : PointedCone R M) : Submodule R M where
  carrier := C ⊓ -C
  add_mem' hx hy := by simpa using ⟨C.add_mem hx.1 hy.1, C.add_mem hy.2 hx.2⟩
  zero_mem' := by simp
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

@[simp] lemma lineal_eq_inter_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by rfl

lemma mem_lineal {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by rfl

@[simp] lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp

lemma lineal_eq_sSup (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C} := by
  rw [le_antisymm_iff]
  constructor
  · exact le_sSup (lineal_le C)
  intro x hx
  have hC : sSup {S : Submodule R M | S ≤ C} ≤ C := by simp
  exact mem_lineal.mpr ⟨hC hx, hC (neg_mem hx : -x ∈ _)⟩


end Ring






namespace IsFaceOf

section Ring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F : PointedCone R M}

lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
  fun _ hx => hF.mem_of_add_mem hx.1 hx.2 (by simp)

lemma lineal_eq (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  constructor <;> intro ⟨hx, hx'⟩
  · exact ⟨hF.le hx, hF.le hx'⟩
  constructor
  · exact hF.mem_of_add_mem hx hx' (by simp)
  · exact hF.mem_of_add_mem hx' hx (by simp)

end Ring

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {C F : PointedCone R M}

/-- The lineality space of a cone is a face. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  apply iff_mem_of_add_mem.mpr
  simp only [PointedCone.lineal_le, Submodule.restrictScalars_mem, true_and]
  intro _ _ xc yc xyf
  simp only [mem_lineal, neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

end Field

end IsFaceOf





namespace Face

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {C F : PointedCone R M}

/-!
### Complete Lattice
-/

-- variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
--   [AddCommGroup N] [Module R N] {C C₁ F : PointedCone R M} {C₂ : PointedCone R N}

/-- The face of a pointed cone `C` that is its lineal space. It is contained in all faces of `C`. -/
def lineal {C : PointedCone R M} : Face C := ⟨C.lineal, IsFaceOf.lineal C⟩

lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := F.isFaceOf.lineal_le

/-- The bottom element of the partial order on faces of `C` is `C.lineal`. -/
instance : OrderBot (Face C) where
  bot := lineal
  bot_le F := F.lineal_le

instance : BoundedOrder (Face C) where

instance : CompleteLattice (Face C) where

end Field

end Face

end PointedCone
