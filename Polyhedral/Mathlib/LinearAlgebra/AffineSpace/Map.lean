import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs

namespace AffineSpace'

section AffineMap

open AffineWeights AffineSpace'

structure AffineMap (R M N : Type*) [Semiring R] [AffineSpace' R M] [AffineSpace' R N] where
  toFun : M → N
  comm  : ∀ w : AffineWeights R M,
    toFun (affineCombination w) = affineCombination (w.map toFun)

namespace AffineMap

variable {R M N : Type*} [Semiring R] [AffineSpace' R M] [AffineSpace' R N]

instance : FunLike (AffineMap R M N) M N where
  coe := fun t => t.toFun
  coe_injective' := fun t s h => by cases t; cases s; simp_all

@[ext]
theorem ext {f g : AffineMap R M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

abbrev id : AffineMap R M M := ⟨_root_.id, by simp [map]⟩

@[simp]
lemma id_toFun (x : M) : (AffineMap.id (R := R)).toFun x = x := rfl

variable {P : Type*} [AffineSpace' R P]
def comp (g : AffineMap R N P) (f : AffineMap R M N) : AffineMap R M P where
  toFun := g.toFun ∘ f.toFun
  comm  := fun w => by simp only [Function.comp, f.comm, g.comm, AffineWeights.map_map]

end AffineMap

structure AffineEquiv (R M N : Type*) [Semiring R] [AffineSpace' R M] [AffineSpace' R N]
    extends AffineMap R M N where
  invFun : AffineMap R N M
  left_inv : invFun.toFun.LeftInverse toFun
  right_inv : invFun.toFun.RightInverse toFun

namespace AffineEquiv

variable {R M N : Type*} [Semiring R] [AffineSpace' R M] [AffineSpace' R N]

instance : FunLike (AffineEquiv R M N) M N where
  coe e := e.toFun
  coe_injective' e₁ e₂ h := by
    cases e₁ with | mk f _ li _ =>
    cases e₂ with | mk f' inv' _ ri' =>
    simp only at h
    have hfg : f = f' := AffineMap.ext (fun x => congr_fun h x)
    subst hfg
    congr 1
    ext y
    convert li (inv'.toFun y)
    rw [ri' y]

@[ext]
theorem ext {f g : AffineEquiv R M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

instance : EquivLike (AffineEquiv R M N) M N where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e₁ e₂ h hh := by
    cases e₁
    cases e₂
    simp_all
    have hfg := AffineMap.ext <| congr_fun h
    subst hfg
    congr 1

abbrev id : AffineEquiv R M M :=
  ⟨AffineMap.id, AffineMap.id,
    Function.leftInverse_iff_comp.mpr rfl, Function.rightInverse_iff_comp.mpr rfl⟩

variable {P : Type*} [AffineSpace' R P]
def trans (e₁ : AffineEquiv R M N) (e₂ : AffineEquiv R N P) : AffineEquiv R M P where
  toAffineMap := e₂.toAffineMap.comp e₁.toAffineMap
  invFun := e₁.invFun.comp e₂.invFun
  left_inv x := by simp [AffineMap.comp, e₂.left_inv (e₁.toFun x), e₁.left_inv x]
  right_inv x := by simp [AffineMap.comp, e₁.right_inv (e₂.invFun.toFun x), e₂.right_inv x]

def symm (e : AffineEquiv R M N) : AffineEquiv R N M :=
  ⟨e.invFun, e.toAffineMap, e.right_inv, e.left_inv⟩

end AffineEquiv

structure AffineEmbedding (R M N : Type*) [Semiring R] [AffineSpace' R M] [AffineSpace' R N]
    extends AffineMap R M N where
  inj' : Function.Injective toFun

namespace AffineEmbedding

variable {R M N : Type*} [Semiring R] [AffineSpace' R M] [AffineSpace' R N]

instance : FunLike (AffineEmbedding R M N) M N where
  coe e := e.toFun
  coe_injective' e₁ e₂ h := by
    cases e₁; cases e₂; have := AffineMap.ext <| congr_fun h; subst this; congr

instance : EmbeddingLike (AffineEmbedding R M N) M N where
  injective' f := f.inj'

end AffineEmbedding

section Translation

variable {R M N : Type*} [Ring R] [AffineSpace' R M] [AffineSpace' R N]

open Finsupp in
/-- A weighting with weight `1` on `x` and `z` and weight `-1` on `y`. -/
noncomputable def sub_add (x y z : M) : AffineWeights R M where
  weights := Finsupp.single x 1 + Finsupp.single y (-1) + Finsupp.single z 1
  total := by
    classical
    simp only [Finset.mem_union, mem_support_iff, coe_add, Pi.add_apply, ne_eq, implies_true,
      sum_add_index, sum_single_index, add_eq_right]
    exact add_neg_cancel 1

open Finsupp in
lemma sub_add_comm (x y z : M) (f : AffineMap R M M) :
  f.toFun (affineCombination (sub_add (R := R) x y z)) =
    affineCombination (sub_add (R := R) (f.toFun x) (f.toFun y) (f.toFun z)) := by
  simp [sub_add, f.comm, map, mapDomain, sum_add_index', sum_single_index, sum_neg_index]

@[simp]
lemma sub_add_same (b : M) (f : AffineMap R M M) :
    affineCombination (sub_add (R := R) (f.toFun b) b b) = f.toFun b := by
  simp [sub_add, AffineSpace'.single]

abbrev isTranslative (f : M → M) :=
  ∀ (a b : M), f a = affineCombination (R := R) (sub_add (f b) b a)

variable (R M) in
/-- An affine translation is an affine bijection that satisfies `f a = f b - b + a`. -/
structure AffineTranslation extends AffineEquiv R M M where
  translative : isTranslative (R := R) toFun

instance : FunLike (AffineTranslation R M) M M where
  coe := fun t => t.toFun
  coe_injective' := fun t s h => by
    cases t; cases s
    simp only [AffineTranslation.mk.injEq]
    ext
    exact congr_fun h _

theorem trans_translative (g : AffineTranslation R M) (f : AffineTranslation R M) :
    isTranslative (R := R) (f.trans g.toAffineEquiv).toFun := by
  intro a b
  simp only [AffineEquiv.trans, AffineMap.comp, Function.comp]
  rw [g.translative (f.toFun b) b, g.translative (f.toFun a) b, f.translative a b]
  congr 1
  ext
  simp [sub_add]
  sorry

theorem invFun_translative (f : AffineTranslation R M) :
    isTranslative (R := R) f.symm := by
  intro a b
  sorry

instance : Add (AffineTranslation R M) where
  add f g := ⟨g.toAffineEquiv.trans f.toAffineEquiv, trans_translative f g⟩

instance : Zero (AffineTranslation R M) where
  zero := ⟨AffineEquiv.id, by simp [isTranslative, sub_add, single]⟩

instance : Neg (AffineTranslation R M) where
  neg a := ⟨a.symm, invFun_translative a⟩

@[simp]
lemma AffineTranslation.zero_toAffineMap :
    (0 : AffineTranslation R M).toAffineMap = AffineMap.id := rfl

instance [Nonempty M] : AddGroup (AffineTranslation R M) where
  add_assoc a b c := by
    simp [HAdd.hAdd, Add.add, AffineEquiv.trans, AffineMap.comp, Function.comp_assoc]
  zero_add a := by simp [HAdd.hAdd, Add.add, AffineEquiv.trans, AffineMap.comp]; rfl
  add_zero a := by simp [HAdd.hAdd, Add.add, AffineEquiv.trans, AffineMap.comp]; rfl
  nsmul := nsmulRec
  neg_add_cancel a := by
    simp only [Neg.neg, HAdd.hAdd, Add.add, AffineEquiv.trans, AffineMap.comp, AffineEquiv.symm,
      show a.invFun.toFun ∘ a.toFun = id by ext x; exact a.left_inv x]
    rfl
  zsmul := zsmulRec

variable {R : Type*} [Ring R] {M : Type*} [af : AffineSpace' R M] in
/-- An AffineSpace' defines an AddTorsor on its affine translations. -/
@[reducible]
public def instAddTorsor [Nonempty M] : AddTorsor (AffineTranslation R M) M where
  vadd v p := v.toFun p
  add_vadd v w p := sorry
  zero_vadd p := sorry
  vsub := sorry
  vsub_vadd' := sorry
  vadd_vsub' := sorry

end Translation

end AffineMap
