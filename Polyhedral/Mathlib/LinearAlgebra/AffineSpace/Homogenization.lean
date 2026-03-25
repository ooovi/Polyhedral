import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Geometry.Convex.Cone.Pointed
import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace Affine

section Ring

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
structure Homogenization extends A →ᵃ[R] W where
  inj : toAffineMap.toFun.Injective
  full (w : W) :
    Xor' (∃ p : A, ∃ c : R, c ≠ 0 ∧ c • w = toAffineMap p)
         (∃ p q : A, w = toAffineMap p - toAffineMap q)

variable (hom : Homogenization R A W)

variable [Nontrivial R] in
theorem embed_ne_zero (x : A) : hom.toAffineMap x ≠ (0 : W) := by
  intro hn
  rcases hom.full (hom.toAffineMap x) with ⟨⟨p, ⟨c, _, jpp⟩⟩, hpp⟩ | ⟨⟨p, q, hpq⟩, hnp⟩
  · simp only [hn, smul_zero] at jpp
    exact hpp ⟨x, p, by simp [hn, jpp]⟩
  · simp only [ne_eq, hn, smul_zero, exists_and_right, exists_and_left, not_and, not_exists,
    forall_exists_index] at hnp
    exact hnp _ one_ne_zero x hn.symm

variable [PartialOrder R] [IsStrictOrderedRing R]
theorem convex_embeds_cone (s : Set A) (iA' : AffineSpace' R A) (hc : AffineSpace'.Convex R s) :
    PointedCone.span R (hom.toAffineMap.toFun '' s) = hom.toAffineMap.toFun '' s := by
  refine eq_of_le_of_ge ?_ ?_
  simp
  intro x xs
  simp at xs ⊢
  rcases hom.full x with ⟨⟨p, ⟨c, ⟨cn0, jpp⟩⟩⟩, hpp⟩ | ⟨⟨p, q, hpq⟩, hnp⟩
  sorry
end Ring


section DivisionRing

variable {R : Type*} [DivisionRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable (hom : Homogenization R A W)

def projectivizationEquiv : Projectivization R V ≃ Set.range hom.toAffineMap where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end DivisionRing
