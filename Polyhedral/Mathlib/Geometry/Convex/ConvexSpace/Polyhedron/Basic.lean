import Mathlib.Algebra.AddTorsor.Defs

import Polyhedral.Polyhedral.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Convexity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice

/-! This file defines polyhedral cones. We chose a definition that also works well
in infinite dimensions and behaves nice w.r.t. duality. In particular, the definition
gives is neither V (FG) nor H (DualFG). -/

namespace Convexity

open ConvexSpace Pointwise

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]

noncomputable local instance : ConvexSpace R A := AddTorsor.toConvexSpace

variable {s : Set V} {t : Set A}

variable (R) in
def IsPolyhedron (P : Set A) : Prop :=
  ∃ C : PointedCone R V, C.IsPolyhedral
    ∧ ∃ Q : Set A, IsPolytope R Q
    ∧ P = (C : Set V) +ᵥ Q

variable {P P₁ P₂ : Set A}

lemma IsPolytope.isPolyhedron (hP : IsPolytope R P) : IsPolyhedron R P :=
  ⟨⊥, PointedCone.IsPolyhedral.bot, P, hP, by simp⟩

lemma IsPolyhedral.isPolyhedron (C : PointedCone R V) (hC : C.IsPolyhedral) :
    IsPolyhedron R (C : Set V) :=
  ⟨C, hC, {0}, by simp⟩

namespace IsPolyhedron

variable (R A) in
protected lemma empty : IsPolyhedron R (∅ : Set A) := ⟨⊥, .bot, ∅, by simp⟩

variable (R) in
protected lemma singleton (x : A) : IsPolyhedron R {x} := ⟨⊥, .bot, {x}, by simp⟩

variable (R A) in
protected lemma univ : IsPolyhedron R (⊤ : Set A) := by
  let x := Classical.arbitrary A
  refine ⟨⊤, .top, {x}, .singleton R x, ?_⟩
  -- TODO: implement `⊤ +ᵥ _ = ⊤` and shorten this proof.
  ext z
  simp only [Set.top_eq_univ, Set.mem_univ, Submodule.top_coe, Set.vadd_singleton, Set.image_univ,
    Set.mem_range, true_iff]
  use z -ᵥ x
  exact vsub_vadd _ _

section Pointwise

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

open Pointwise

protected lemma vadd {P₁ : Set V} {P₂ : Set A} (hP₁ : IsPolyhedron R P₁) (hP₂ : IsPolyhedron R P₂) :
    IsPolyhedron R (P₁ +ᵥ P₂) := by
  obtain ⟨C₁, hC₁, Q₁, hQ₁, rfl⟩ := hP₁
  obtain ⟨C₂, hC₂, Q₂, hQ₂, rfl⟩ := hP₂
  rw [vadd_eq_add, ← add_vadd, add_comm, ← add_assoc, add_vadd]
  use C₂ + C₁
  constructor
  · sorry -- TODO: missing lemma for polyhedral cones
  use Q₁ +ᵥ Q₂
  constructor
  · apply IsPolytope.vadd
    · sorry -- exact hQ₁ -- ERROR
    /- TODO: error with convex space diamond. The convex space structure on a module must be the
      the same as the one inferred via `AddTorsor.toConvexSpace` (if the module is considered as
      an affine space). Though I don't understand why this comes up here. -/
    · exact hQ₂
  congr
  -- TODO: prove this once we have `coe_add` for cones.
  sorry

protected lemma add {P₁ P₂ : Set V} (hP₁ : IsPolyhedron R P₁) (hP₂ : IsPolyhedron R P₂) :
  IsPolyhedron R (P₁ + P₂) := .vadd hP₁ hP₂

end Pointwise

section IsModuleConvexSpace

variable [ConvexSpace R V] [IsModuleConvexSpace R V]

lemma isConvexSet (hP : IsPolyhedron R P) : IsConvexSet R P := by
  obtain ⟨C, hC, K, hK, rfl⟩ := hP
  exact .vadd C.isConvexSet hK.isConvexSet

end IsModuleConvexSpace

end IsPolyhedron

end Convexity
