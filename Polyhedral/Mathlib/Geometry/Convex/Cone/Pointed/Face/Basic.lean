/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Quotient.Basic

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual
-- import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Field
-- import Polyhedral.Halfspace


/-!
# Faces of pointed cones
-/

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
in
structure IsFaceOf (F C : PointedCone R M) where
  subset : (F : Set M) ⊆ C -- better F ≤ C ?
  left_mem_of_smul_add_mem :
    ∀ x ∈ C, ∀ y ∈ C, ∀ a > (0 : R), ∀ b > (0 : R), a • x + b • y ∈ F → x ∈ F

namespace IsFaceOf
-- M: I think using a namespae here is bad

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}

@[refl]
lemma refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun ⦃_⦄ a ↦ a, fun _ hx _ _ _ _ _ _  _ ↦ hx⟩
lemma rfl {C : PointedCone R M} : C.IsFaceOf C := ⟨fun ⦃_⦄ a ↦ a, fun _ hx _ _ _ _ _ _ _ ↦ hx⟩


-- theorem inter (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) :
--     F.IsFaceOf (C₁ ⊓ C₂) := by
--   use fun x xf => Submodule.mem_inf.mpr ⟨h₁.subset xf, h₂.subset xf⟩
--   intro x xi y yi a a0 b b0 h
--   refine h₁.left_mem_of_smul_add_mem x ?_ y ?_ a a0 b b0 h
--   · exact (Submodule.mem_inf.mp xi).1
--   · exact (Submodule.mem_inf.mp yi).1

theorem inter (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C := by
  use fun x xi => h₁.subset (Submodule.mem_inf.mp xi).1
  intro x xi y yi a a0 b b0 h
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact h₁.left_mem_of_smul_add_mem x xi y yi a a0 b b0 (Submodule.mem_inf.mp h).1
  · exact h₂.left_mem_of_smul_add_mem x xi y yi a a0 b b0 (Submodule.mem_inf.mp h).2


lemma trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  refine ⟨h₁.subset.trans h₂.subset, fun x hx y hy a a0 b b0 h ↦ ?_⟩
  refine h₁.2 _ (h₂.2 _ hx _ hy a a0 b b0 (h₁.subset h)) y ?_ a a0 b b0 h
  refine h₂.left_mem_of_smul_add_mem _ hy _ hx b b0 a a0 ?_
  rw [add_comm] at h
  exact h₁.subset h

lemma le {F : PointedCone R M} (hF : F.IsFaceOf C) : F ≤ C := hF.subset

-- M: better name?
alias le_self := le

-- M: better name?
-- alias le_self := le

lemma face_inf_isFaceOf_inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.subset, Set.inter_subset_right.trans h₂.subset⟩
  simp only [Submodule.mem_inf, gt_iff_lt, and_imp]
  intros x xc₁ xc₂ y yc₁ yc₂ a a0 b b0 hz₁ hz₂
  constructor
  · exact h₁.left_mem_of_smul_add_mem x xc₁ y yc₁ a a0 b b0 hz₁
  · exact h₂.left_mem_of_smul_add_mem x xc₂ y yc₂ a a0 b b0 hz₂

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) :
    (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  face_inf_isFaceOf_inf h rfl

lemma isExtreme (h : F.IsFaceOf C) : IsExtreme R (E := M) C F := by
  refine ⟨h.subset, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.left_mem_of_smul_add_mem x xc y yc a a0 b b0
  rwa [← hz] at zf

end Semiring

/-!
### Joins
-/

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C D F G : PointedCone R M}

lemma sup_isFaceOf_sup (hFC : F.IsFaceOf C) (hGD : G.IsFaceOf D)
    (hCD : ∀ {x}, x ∈ Submodule.span R C ∧ x ∈ Submodule.span (M := M) R D → x = 0) :
    (F ⊔ G).IsFaceOf (C ⊔ D) := by
  constructor
  · simp only [SetLike.coe_subset_coe, sup_le_iff]
    constructor
    · apply le_trans _ le_sup_left
      convert hFC.subset
    · apply le_trans _ le_sup_right
      convert hGD.subset
  · simp; intros x xm y ym a a0 b b0 hab _ _
    sorry

    -- wlog h : ¬(x ∈ Submodule.span R (SetLike.coe C) ∧ x ∈ Submodule.span R (SetLike.coe D))
    -- · push_neg at h
    --   have := hCD h
    --   subst this
    --   exact zero_mem _
    -- · push_neg at h
    --   obtain ⟨xC, xCM, xD, xDM, xx⟩ := Submodule.mem_sup.mp xm
    --   obtain ⟨yC, yCM, yD, yDM, yy⟩ := Submodule.mem_sup.mp ym
    --   obtain ⟨zF, zFM, zG, zGM, zz⟩ := Submodule.mem_sup.mp zu

    --   have : zF ∈ openSegment R xC yC ∧ zG ∈ openSegment R xD yD := by
    --     rw [openSegment, Set.mem_setOf, ← xx, ← yy, ← zz] at zo
    --     obtain ⟨a, b, a0, b0, ab1, abz⟩ := zo
    --     have : (a • xC + b • yC) + (a • xD + b • yD) = zF + zG := by
    --       rw [← abz, smul_add, smul_add]
    --       abel

    --     let mem {C : PointedCone R  M} {x y} (xCM yCM) : a • x + b • y ∈ C :=
    --       C.add_mem (C.smul_mem (le_of_lt a0) xCM) (C.smul_mem (le_of_lt b0) yCM)

    --     have := uniq_decomp_of_zero_inter
    --       (mem xCM yCM) (hFC.subset zFM) (mem xDM yDM) (hGD.subset zGM) hCD this
    --     constructor
    --     use a, b, a0, b0, ab1, this.1
    --     use a, b, a0, b0, ab1, this.2

    --   apply Submodule.mem_sup.mpr
    --   use xC, hFC.left_mem_of_smul_add_mem xCM yCM zFM this.1
    --   use xD, hGD.left_mem_of_smul_add_mem xDM yDM zGM this.2

-- lemma iff_mem_of_add_mem' :
--     F.IsFaceOf C ↔ F ≤ C ∧ ∀ x ∈ C, ∀ y ∈ C, x + y ∈ F → x ∈ F := by
--   constructor <;> intro h
--   · refine ⟨h.subset, ?_⟩
--     intros x xC y yC xy
--     have := h.left_mem_of_smul_add_mem xC yC (z := ((one : M) + 1)⁻¹ * (x + y))
--     sorry
--   · refine ⟨h.1, ?_⟩
--     intros x xC y yC z zF zo
--     simp [openSegment] at zo
--     obtain ⟨a, a0, b, b0, ab, abz⟩ := zo
--     rw [← abz] at zF
--     have := h.2 _ (smul_mem _ (le_of_lt a0) xC) _ (smul_mem _ (le_of_lt b0) yC)
--     have := h.2 x xC (- x + z)


    -- apply iff_mem_of_mul_add_mem.mpr ⟨h.1, fun x xC y yC c c0 hcxy => ?_⟩
    -- have cxF := h.2 (c • x) (smul_mem _ (le_of_lt c0) xC) y yC hcxy
    -- convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    -- simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel c (by positivity)]

-- M: better name
alias sup := sup_isFaceOf_sup

-- M: Where is inf?

end Ring

section foo
variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/-- The lineal space of a cone `C` is a face of `C`. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  suffices ∀ x ∈ C, ∀ y ∈ C, x + y ∈ ↑C.lineal → x ∈ ↑C.lineal by
    sorry -- exact iff_mem_of_add_mem.mpr ⟨PointedCone.lineal_le C, this⟩
  intros _ xc _ yc xyf
  simp only [lineal_mem, neg_add_rev, xc, true_and] at xyf ⊢
  have := add_mem xyf.2 yc
  simp only [neg_add_cancel_comm] at this
  assumption

lemma lineal_le {C : PointedCone R M} (h : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ F → x ∈ F ) : C.lineal ≤ F := by
  intro x xl
  apply lineal_mem.mp at xl
  exact h x xl.1 (-x) xl.2 (by simp only [add_neg_cancel, zero_mem])

end foo

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/-!
### Equivalent definitions of isFaceOf on fields
-/

lemma iff_mem_of_mul_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ x ∈ C, ∀ y ∈ C, ∀ c : R, 0 < c → c • x + y ∈ F → x ∈ F := by
  constructor
  · intro f; refine ⟨f.subset, ?_⟩
    intros x xC y yC c cpos h
    apply f.left_mem_of_smul_add_mem x xC y yC c cpos 1 zero_lt_one
    simp [h]
  · intro h
    constructor
    · exact h.1
    · intros x xC y yC a a0 b b0 hab
      exact h.2 x xC (b • y) (Submodule.smul_mem C ⟨b, le_of_lt b0⟩ yC) a a0 hab

lemma iff_mem_of_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ x ∈ C, ∀ y ∈ C, x + y ∈ F → x ∈ F := by
  constructor <;> intro h
  · have := iff_mem_of_mul_add_mem.mp h
    refine ⟨this.1, fun x xC y yC => ?_⟩
    convert this.2 x xC y yC 1 (zero_lt_one)
    simp
  · apply iff_mem_of_mul_add_mem.mpr ⟨h.1, fun x xC y yC c c0 hcxy => ?_⟩
    have cxF := h.2 (c • x) (smul_mem _ (le_of_lt c0) xC) y yC hcxy
    convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel c (by positivity)]

lemma span_nonneg_lc_mem {f : F.IsFaceOf (span R s)} {n : ℕ} {c : Fin n → { c : R // 0 ≤ c }}
    {g : Fin n → s} (h : ∑ i, c i • (g i).val ∈ F) {i : Fin n} (cpos : 0 < c i) :
    (g i).val ∈ F := by
  induction n with
  | zero => exact isEmptyElim i
  | succ n ih =>
      have : ∑ i ∈ {i}ᶜ, c i • (g i).val ∈ span R s :=
        Submodule.sum_smul_mem _ _ (fun _ _ => subset_span (Subtype.coe_prop _))
      rw [Fintype.sum_eq_add_sum_compl i] at h
      exact (iff_mem_of_mul_add_mem.mp f).2 _ (subset_span (Subtype.coe_prop _)) _ this _ cpos h

lemma iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  constructor
  · exact IsFaceOf.le
  · rw [iff_mem_of_mul_add_mem] at ⊢ h₁
    exact fun h => ⟨h, fun x hx y hy => h₁.2 x (h₂.le hx) y (h₂.le hy)⟩

lemma iff_of_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₁) :
    F₂.IsFaceOf C ↔ F₂.IsFaceOf F₁ :=
  ⟨fun h => (iff_le h h₁).mpr h₂, fun h => trans h h₁⟩

end Field

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {C F : PointedCone R M}

/-- Mapping a face using an injective linear map yields a face of the image of `C`. -/
lemma map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := by
  simp only [iff_mem_of_add_mem, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ← map_add, hf.eq_iff, exists_eq_right]
  constructor <;> intro ⟨sub, hF⟩
  · refine ⟨fun x xf => ?_, fun x hx y hy hxy => hF x hx y hy _ hxy (hf (Eq.refl _))⟩
    obtain ⟨y, yC, hy⟩ := Submodule.mem_map.mp <| sub (Submodule.mem_map_of_mem xf)
    rw [hf hy] at yC
    assumption
  · refine ⟨Submodule.map_mono sub, fun x hx y hy z hz h => ?_⟩
    subst h
    exact hF x hx y hy hz

lemma map {f : M →ₗ[R] N} (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (map f F).IsFaceOf (map f C) := (map_iff hf).mpr hF

lemma map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) := hF.map e.injective

/-- The preimage of a face under a surjective linear map is a face of the preimage of `C`. -/
lemma comap_iff {f : N →ₗ[R] M} (hf : Function.Surjective f) :
    (PointedCone.comap f F).IsFaceOf (.comap f C) ↔ F.IsFaceOf C := by
  simp only [iff_mem_of_add_mem, mem_comap, map_add]
  have ec (x : M) := Function.invFun_eq (hf x)
  constructor <;> intro ⟨sub, hF⟩
  · constructor
    · intro x xF
      apply Submodule.map_le_iff_le_comap.mpr sub
      simp only [Submodule.mem_map, mem_comap, LinearMap.coe_restrictScalars]
      use Function.invFun f x
      rw [ec]
      exact ⟨xF, Eq.refl _⟩
    · intro x xC y yC h
      rw [← ec x] at h xC ⊢
      rw [← ec y] at h yC
      refine hF (Function.invFun f x) xC (Function.invFun f y) yC h
  · exact ⟨Submodule.comap_mono sub, fun x hx y hy h => hF _ hx _ hy h⟩

lemma comap {f : N →ₗ[R] M} (hf : Function.Surjective f) (hF : F.IsFaceOf C) :
    (comap f F).IsFaceOf (comap f C) := (comap_iff hf).mpr hF

lemma comap_equiv (e : N ≃ₗ[R] M) (hF : F.IsFaceOf C) :
    (PointedCone.comap (e : N →ₗ[R] M) F).IsFaceOf (.comap e C) := hF.comap e.surjective

end Field

end IsFaceOf

/-!
## Bundled Face
-/


variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
in
/-- A face of a pointed cone `C` is a pointed cone that is an extreme subset of `C`. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C : PointedCone R M} {F F₁ F₂ : Face C}

def self (C : PointedCone R M) : Face C := ⟨_, IsFaceOf.refl C⟩

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) :=
    ⟨Face.self C⟩
instance {S : Submodule R M} : CoeDep (Submodule R M) S (Face (S : PointedCone R M)) :=
    ⟨(S : PointedCone R M)⟩

-- does not work without the second CoeDep
example {S : Submodule R M} : Face (S : PointedCone R M) := S

-- we can't have an actual Coe instance because coercion target throws away the information `C`
@[coe, simp]
def toPointedCone {C : PointedCone R M} (F : Face C) := F.toSubmodule

instance : CoeOut (Face (M := M) (R := R) C) (PointedCone R M) where
  coe := toPointedCone

instance : SetLike (Face C) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

@[ext] lemma ext (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp]
theorem toPointedCone_le_iff {F₁ F₂ : Face C} : F₁ ≤ F₂ ↔ F₁.toPointedCone ≤ F₂.toPointedCone := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

@[simp] lemma mem_toPointedCone {F : Face C} (x : M) : x ∈ F ↔ x ∈ F.toPointedCone := .rfl

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h

end Semiring

/-!
### Operations on faces
-/

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C : PointedCone R M}

/-- The face of `C` obtained by intersecting two of `C`'s faces. -/
def inter (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, IsFaceOf.inter F₁.isFaceOf F₂.isFaceOf⟩

/-- The face of `C` obtained by embedding a face of a face of `C`. -/
def embed {F₁ : Face C} (F₂ : Face (F₁ : PointedCone R M)) : Face C :=
    ⟨F₂, F₂.isFaceOf.trans F₁.isFaceOf⟩

/-- A face of a face of `C` coerces to a face of `C`. -/
instance {F : Face C} : CoeOut (Face (F : PointedCone R M)) (Face C) := ⟨Face.embed⟩

/-!
#### Product
-/
section Prod

variable {N : Type*} [AddCommGroup N] [Module R N] {C₁ : PointedCone R M} {C₂ : PointedCone R N}

/-- The face of `C₁ × C₂` obtained by taking the product of faces `F₁ ≤ C₁` and `F₂ ≤ C₂`. -/
def prod (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) := by
  refine ⟨Submodule.prod F₁ F₂, ⟨?_, ?_⟩⟩
  · simp only [Submodule.prod_coe, Set.prod_subset_iff, SetLike.mem_coe, Set.mem_prod]
    exact fun _ a _ b => ⟨F₁.isFaceOf.subset a, F₂.isFaceOf.subset b⟩
  · simp only [Submodule.mem_prod, gt_iff_lt, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
    intros x₁ x₂ xc₁ xc₂ y₁ y₂ yc₁ yc₂ a a0 b b0 hab₁ hab₂
    constructor
    · exact F₁.isFaceOf.left_mem_of_smul_add_mem _ xc₁ _ yc₁ a a0 b b0 hab₁
    · exact F₂.isFaceOf.left_mem_of_smul_add_mem _ xc₂ _ yc₂ a a0 b b0 hab₂

/-- The face of `C₁` obtained by projecting to the left component of a face `F ≤ C₁ × C₂`. -/
def prod_left (F : Face (C₁.prod C₂)) : Face C₁ := {
  Submodule.map (LinearMap.fst _ M N) F with
  isFaceOf := by
    constructor
    · simp only [Submodule.map_coe, LinearMap.fst_apply, Set.image_subset_iff]
      exact le_trans F.isFaceOf.subset (fun _ xc => (Set.mem_prod.mp xc).1)
    · simp
      intros x xc y yc a a0 b b0 z hab
      use z
      -- have zzc : zz ∈ C₂ := (Set.mem_prod.mpr (F.isFaceOf.subset zf)).2
      refine F.isFaceOf.left_mem_of_smul_add_mem (y := (y, z)) _ ?_ ?_ a a0 b b0 ?_
      · exact Set.mem_prod.mpr ⟨xc, sorry⟩
      · exact Set.mem_prod.mpr ⟨yc, sorry⟩
      · sorry
}

/-- The face of `C₂` obtained by projecting to the right component of a face `F ≤ C₁ × C₂`. -/
def prod_right (F : Face (C₁.prod C₂)) : Face C₂ := {
  Submodule.map (LinearMap.snd _ M N) F with
  isFaceOf := by
    constructor
    · simp only [Submodule.map_coe, LinearMap.snd_apply, Set.image_subset_iff]
      exact le_trans F.isFaceOf.subset (fun _ xc => (Set.mem_prod.mp xc).2)
    · simp
      intros x xc y yc a a0 b b0 h
      sorry
      -- have zzc : zz ∈ C₁ := (Set.mem_prod.mpr (F.isFaceOf.subset sorry)).1
      -- refine ⟨zz, F.isFaceOf.left_mem_of_smul_add_mem (y := (zz, y)) ?_ ?_ zf ?_⟩
      -- · exact Set.mem_prod.mpr ⟨zzc, xc⟩
      -- · exact Set.mem_prod.mpr ⟨zzc, yc⟩
      -- · rw [← Prod.image_mk_openSegment_right zz x y]
      --   exact ⟨_, zo, rfl⟩
  }

@[simp]
lemma prod_prod_left (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_left = F₁ := by
  simp [prod_left, prod]

@[simp]
lemma prod_prod_right (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_right = F₂ := by
  simp [prod_right, prod]

@[simp]
lemma prod_left_prod_right (G : Face (C₁.prod C₂)) : G.prod_left.prod G.prod_right = G := by
  simp only [prod_right, prod_left, prod]
  ext x
  constructor
  · rintro ⟨a, c⟩
    simp only [mem_toPointedCone, toPointedCone]
    --simp only [Submodule.map_coe, LinearMap.fst_apply, LinearMap.snd_apply, Set.mem_image] at a c
    obtain ⟨a, b', c'⟩ := a
    obtain ⟨a', b, c⟩ := c
    have : x = (a.1, a'.2) := by exact Prod.ext (Eq.symm c') (Eq.symm c)
    rw [this]
    -- have := G.isFaceOf.left_mem_of_smul_add_mem sorry (G.isFaceOf.subset b')
    -- have := (Submodule.mem_prod.mp <| G.isFaceOf.subset d).2
    sorry
  · simp; intro h; exact ⟨⟨x.2, h⟩, ⟨x.1, h⟩⟩

end Prod

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ C₂ F : PointedCone R M} {s t : Set M}

/-!
#### Restrict
-/
abbrev span (F : Face C) : Submodule R M := Submodule.span R F

/-- The face of `F₁` obtained by intersecting `F₁` with another of `C`'s faces. -/
def restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
  ⟨F₁ ⊓ F₂, (F₁.isFaceOf.iff_of_le inf_le_left).mp (F₁.isFaceOf.inter F₂.isFaceOf)⟩

/-!
#### Map and comap
-/
/-- The face `map f F` of `map f C`. -/
def map {f : M →ₗ[R] N} (hf : Function.Injective f) (F : Face C) : Face (map f C)
    := ⟨_, F.isFaceOf.map hf⟩

/-- The face `map e F` of `map e C`. -/
def map_equiv (e : M ≃ₗ[R] N) (F : Face C) : Face (PointedCone.map (e : M →ₗ[R] N) C)
    := F.map e.injective

lemma map_inj (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (map hf : Face C → Face _) := by
  intros F₁ F₂ h
  simp [map] at h
  ext x; constructor <;> intro hx
  · have : f x ∈ PointedCone.map f F₁.toSubmodule := mem_map.mpr ⟨x, ⟨hx, rfl⟩⟩
    rw [h] at this
    obtain ⟨y, yF₂, fy⟩ := Submodule.mem_map.mp this
    simpa [← hf fy]
  · have : f x ∈ PointedCone.map f F₂.toSubmodule := mem_map.mpr ⟨x, ⟨hx, rfl⟩⟩
    rw [← h] at this
    obtain ⟨y, yF₂, fy⟩ := Submodule.mem_map.mp this
    simpa [← hf fy]

/-- The face `comap f F` of `comap f C`. -/
def comap {f : N →ₗ[R] M} (hf : Function.Surjective f) (F : Face C) : Face (comap f C)
    := ⟨_, F.isFaceOf.comap hf⟩

/-- The face `comap e F` of `comap e C`. -/
def comap_equiv (e : N ≃ₗ[R] M) (F : Face C) : Face (PointedCone.comap (e : N →ₗ[R] M) C)
    := F.comap e.surjective

end Field

end Face

/-!
### Intersections
-/
section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F : PointedCone R M} {s t : Set M}

lemma span_inter_face_span_inf_face (F : Face (span R s)) :
    span R (s ∩ F) = (span R s) ⊓ F := by
  ext x; constructor
  · simp [Submodule.mem_span]
    exact fun h =>
      ⟨fun p sp => h p (subset_trans Set.inter_subset_left sp), h F Set.inter_subset_right⟩
  · intro h
    apply Submodule.mem_inf.mp at h
    obtain ⟨n, c, g, xfg⟩ := Submodule.mem_span_set'.mp h.1
    subst xfg
    apply Submodule.sum_mem
    intro i _
    by_cases hh : c i = 0
    · rw [hh]; simp
    · apply Submodule.smul_mem; apply Submodule.subset_span
      have := F.isFaceOf.span_nonneg_lc_mem h.2 (pos_of_ne_zero hh)
      exact Set.mem_inter (Subtype.coe_prop (g i)) this

-- If span R s and span R t are disjoint (only share 0)
example (h : Submodule.span R s ⊓ Submodule.span R t = ⊥)
    (hs : s ⊆ Submodule.span R s) (ht : t ⊆ Submodule.span R t) :
    Submodule.span R (s ∩ t) = Submodule.span R s ⊓ Submodule.span R t := by
  -- When intersection is ⊥, both sides equal ⊥ if s ∩ t = ∅
  sorry

lemma exists_span_subset_face (F : Face (span R s)) :
    ∃ t ⊆ s, span R t = F := by
  use s ∩ F
  constructor
  · exact Set.inter_subset_left
  · simp [span_inter_face_span_inf_face F]
    exact F.isFaceOf.subset

lemma exists_fg_span_subset_face {s : Finset M} (F : Face (span R s.toSet)) :
    ∃ t ⊆ s, span R t.toSet = F := by
  use (s.finite_toSet.inter_of_left F).toFinset
  constructor
  · simp
  · simp [span_inter_face_span_inf_face F]
    exact F.isFaceOf.subset

lemma FG.face_fg_of_fg (hC : C.FG) (F : Face C) : F.FG := by
  obtain ⟨_, rfl⟩ := hC
  let ⟨t, _, tt⟩ := exists_fg_span_subset_face F
  use t, tt

/-- An FG cone has finitely many faces. -/
theorem Face.finite_of_fg (hC : C.FG) : Finite (Face C) := by
  obtain ⟨s, rfl⟩ := hC
  apply Finite.of_injective (β := Finset.powerset s)
    fun F => ⟨(exists_fg_span_subset_face F).choose,
               by simp; exact (exists_fg_span_subset_face _).choose_spec.1⟩
  intros F F' FF
  have := congrArg (fun s : s.powerset => PointedCone.span (E := M) R s) FF
  simp [(exists_fg_span_subset_face _).choose_spec.2] at this
  exact Face.toPointedCone_eq_iff.mp this

-- TODO: move the below to the other lineal lemmas.

lemma span_inter_lineal_eq_lineal' (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  convert span_inter_face_span_inf_face ⟨_, IsFaceOf.lineal _⟩
  simp

lemma FG.lineal_fg' {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by
  convert FG.face_fg_of_fg hC ⟨_, IsFaceOf.lineal _⟩
  simp

end Field

/-!
### Faces of the dual cone
-/

section CommRing

variable [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R) {C : PointedCone R M}

def subdual (C F : PointedCone R M) : PointedCone R N :=
  (dual p C) ⊓ (.dual p F : Submodule R N)

lemma subdual_antitone : Antitone (subdual p C) := by
  intros _ _ hF
  unfold subdual
  gcongr
  exact Submodule.dual_le_dual hF

end CommRing

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R) {C F : PointedCone R M}

/-- The subdual of a face is a face of the dual. -/
lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  apply iff_mem_of_add_mem.mpr ⟨by simp, ?_⟩
  intros x xd
  simp only [mem_dual, SetLike.mem_coe, Submodule.mem_inf, map_add, Submodule.restrictScalars_mem,
    Submodule.mem_dual, xd, true_and, and_imp]
  intros _ yC _ n'on _ mF
  apply eq_of_le_of_ge
  · exact xd (hF.subset mF)
  · rw [n'on mF]
    exact (le_add_iff_nonneg_right _).mpr <| yC (hF.subset mF)

/-- The face of the dual cone that corresponds to this face. -/
def Face.dual (F : Face C) : Face (dual p C) := ⟨_, F.isFaceOf.subdual_dual p⟩

lemma Face.dual_antitone : Antitone (dual p : Face C → Face _) :=
  fun _ _ hF _ xd => subdual_antitone p (toPointedCone_le_iff.mpr hF) xd

section IsDualClosed

variable (hC : C.IsDualClosed p)

/-- The subdual is injective. -/
-- only for fg
lemma subdual_inj : Function.Injective (subdual p C) := sorry

/-- The subdual is involutive. -/
-- only for fg
lemma subdual_subdual : subdual p.flip (dual p C) (subdual p C F) = F := sorry

/-- The subdual is strictly antitone. -/
lemma subdual_antitone_iff {F₁ F₂ : PointedCone R M} :
    subdual p C F₁ ≤ subdual p C F₂ ↔ F₂ ≤ F₁ where
  mpr := fun h => subdual_antitone p h
  mp := sorry

end IsDualClosed

end Field

end PointedCone
