/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/


import Mathlib.Analysis.Convex.Extreme
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

/-!
# Faces of pointed cones

This file defines what it means for a pointed cone to be a face of another pointed cone and
establishes basic properties of this relation.
A subcone `F` of a cone `C` is a face if any two points in `C` that have a positive combination
in `F` are also in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We prove that every face is an extreme set of its cone. We do not use `IsExtreme` as a
  definition because this is an affine notion and does not allow the flexibility necessary to
  deal wth cones over general rings. E.g. the cone of positive integers has no proper subset that
  are extreme.
* Most results proven over a field hold more generally over an Archimedean ring. In particular,
  `iff_mem_of_add_mem` holds whenever for every `x ∈ R` there is a `y ∈ R` with `1 ≤ x * y`.

-/

open Submodule

@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
/-- A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` with a strictly
positive combination in `F` are also in `F`. -/
structure IsFaceOf (F C : PointedCone R M) where
  le : F ≤ C
  mem_of_smul_add_mem :
    ∀ {x y : M} {a : R}, x ∈ C → y ∈ C → 0 < a → a • x + y ∈ F → x ∈ F

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

theorem isFaceOf_iff_mem_of_smul_add_smul_mem : F.IsFaceOf C ↔
    (F ≤ C ∧ ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F)
    := by
  constructor <;> intro h
  · refine ⟨h.1, fun xC yC a0 b0 hab => ?_⟩
    exact h.2 xC (Submodule.smul_mem C ⟨_, le_of_lt b0⟩ yC) a0 hab
  · refine ⟨h.1, ?_⟩
    by_cases hc : 0 < (1 : R)
    · intros xc yc a0 haxy
      exact h.2 xc yc a0 hc (by simpa)
    · simp [(subsingleton_of_zero_eq_one (zero_le_one.eq_or_lt.resolve_right hc)).eq_zero]

namespace IsFaceOf

/-- A pointed cone `C` as a face of itself. -/
@[refl, simp]
theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

protected theorem rfl {C : PointedCone R M} : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  rw [isFaceOf_iff_mem_of_smul_add_smul_mem] at h₁ h₂ ⊢
  refine ⟨h₁.1.trans h₂.1, fun hx hy a0 b0 h ↦ ?_⟩
  exact h₁.2 (h₂.2 hx hy a0 b0 (h₁.1 h)) (h₂.2 hy hx b0 a0 (by rw [add_comm]; exact h₁.1 h)) a0 b0 h

/-- A face of a cone is a face of another if and only if they are contained in each other. -/
theorem iff_le_of_isFaceOf (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  refine ⟨IsFaceOf.le, fun h => ?_⟩
  rw [isFaceOf_iff_mem_of_smul_add_smul_mem] at ⊢ h₁
  exact ⟨h, fun hx hy => h₁.2 (h₂.le hx) (h₂.le hy)⟩

/-- A face of a cone is an extreme subset of the cone. -/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  apply isFaceOf_iff_mem_of_smul_add_smul_mem.mp at h
  refine ⟨h.1, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.2 xc yc a0 b0
  rwa [← hz] at zf

/-- The intersection of two faces of two cones is a face of the intersection of the cones. -/
theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

/-- The intersection of two faces of a cone is a face of the cone. -/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  inf_idem C ▸ inf h₁ h₂

/-- If a cone is a face of two cones simultaneously, then it's also a face of their intersection. -/
theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) :=
  inf_idem F ▸ inf h₁ h₂

theorem mem_of_add_mem (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : x ∈ F := by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one

theorem mem_add_iff (hF : F.IsFaceOf C) {x y : M} (hx : x ∈ C) (hy : y ∈ C) :
    x + y ∈ F ↔ x ∈ F ∧ y ∈ F := by
  refine ⟨?_, fun ⟨hx, hy⟩ => F.add_mem hx hy⟩
  exact fun h => ⟨mem_of_add_mem hF hx hy h, mem_of_add_mem hF hy hx (by rwa [add_comm])⟩

theorem sum_mem_iff_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i, f i ∈ C) : ∑ i, f i ∈ F ↔ ∀ i, f i ∈ F := by
  classical
  refine ⟨fun hs i => ?_, fun a ↦ Submodule.sum_mem F fun c _ => a c⟩
  refine hF.mem_of_add_mem (hsC i) (sum_mem (fun j (_ : j ∈ Finset.univ.erase i) => hsC j)) ?_
  simp [hs]

section Map

variable [AddCommGroup N] [Module R N]

/-- The image of a face of a cone under an injective linear map is a face of the
  image of the cone. -/
theorem map (f : M →ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (F.map f).IsFaceOf (C.map f) := by
  refine ⟨map_mono hF.le, ?_⟩
  simp only [mem_map, forall_exists_index, and_imp]
  intro _ _ a b bC fbx _ cC fcy ha _ x'F h
  refine ⟨b, ?_, fbx⟩
  apply hF.mem_of_smul_add_mem bC cC ha
  convert x'F
  apply hf
  simp [h, fbx, fcy]

/-- The image of a face of a cone under an equivalence is a face of the image of the cone. -/
theorem map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (F.map (e : M →ₗ[R] N)).IsFaceOf (C.map e) := hF.map _ e.injective

/-- The comap of a face of a cone under a linear map is a face of the comap of the cone. -/
theorem comap (f : N →ₗ[R] M) (hF : F.IsFaceOf C) : (F.comap f).IsFaceOf (C.comap f) := by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem

theorem of_comap_surjective {f : N →ₗ[R] M} (hf : Function.Surjective f)
    (hc : (F.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C := by
  constructor
  · intro x xF
    rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · intro x y a xC yC a0 h
    rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

end Map

end IsFaceOf

lemma face_faces (h : F.IsFaceOf C) :
    F₁.IsFaceOf F ↔ F₁ ≤ F ∧ F₁.IsFaceOf C :=
  ⟨fun h' => ⟨h'.le, h'.trans h⟩,
    fun h' => ⟨h'.1, fun x y ha hs => h'.2.mem_of_smul_add_mem (h.le x) (h.le y) ha hs⟩⟩

variable [AddCommGroup N] [Module R N] in
/-- The image of a cone `F` under an injective linear map is a face of the
  image of another cone `C` if and only if `F` is a face of `C`. -/
theorem isFaceOf_map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C := by
  refine ⟨?_, IsFaceOf.map _ hf⟩
  · intro ⟨sub, hF⟩
    refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
    · obtain ⟨y, yC, hy⟩ := mem_map.mp <| sub (mem_map_of_mem xf)
      rwa [hf hy] at yC
    · simp only [mem_map, forall_exists_index, and_imp] at hF
      obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
      convert hx'
      exact hf hhx'.symm

variable [AddCommGroup N] [Module R N] in
/-- The comap of a cone `F` under a surjective linear map is a face of the
  comap of another cone `F` if and only if `F` is a face of `C`. -/
theorem isFaceOf_comap_iff {f : N →ₗ[R] M} (hf : Function.Surjective f) :
    (F.comap f).IsFaceOf (C.comap f) ↔ F.IsFaceOf C := by
  refine ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

end Semiring

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {G : PointedCone R M} {S : Submodule R M}
variable {H : PointedCone R (M ⧸ S)}

namespace IsFaceOf

/-- Pulling back a face of `G.quot S` gives a face of `G`. -/
lemma inf_comap_mkQ (hH : H.IsFaceOf (G.quot S)) :
    (G ⊓ PointedCone.comap S.mkQ H).IsFaceOf G := by
  refine ⟨inf_le_left, ?_⟩
  intro x y a hxG hyG ha hxy
  refine ⟨hxG, ?_⟩
  change S.mkQ x ∈ H
  exact hH.mem_of_smul_add_mem
    ((PointedCone.mem_map).2 ⟨x, hxG, rfl⟩)
    ((PointedCone.mem_map).2 ⟨y, hyG, rfl⟩)
    ha
    (by simpa [PointedCone.comap, LinearMap.map_smul, LinearMap.map_add] using hxy.2)


end IsFaceOf
end Ring

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

theorem isFaceOf_iff_mem_of_add_mem : F.IsFaceOf C ↔
    (F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F) := by
  constructor <;> intro h
  · exact ⟨h.le, IsFaceOf.mem_of_add_mem h⟩
  · refine ⟨h.1, ?_⟩
    intro x y a xC yC a0 haxy
    have haxF := h.2 (smul_mem _ (le_of_lt a0) xC) yC haxy
    have hxF : (a⁻¹ : R) • (a • x) ∈ F := smul_mem _ (inv_nonneg.mpr (le_of_lt a0)) haxF
    have hxF' := hxF
    rw [← smul_assoc] at hxF'
    have hxF'' : ((1 : R) • x) ∈ F := by simpa [inv_mul_cancel₀ (ne_of_gt a0)] using hxF'
    simpa using hxF''

namespace IsFaceOf

/-- If the positive combination of points of a cone is in a face, then all the points are
  in the face. -/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → R}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i : ι, c i • f i ∈ F)
    (i : ι) (hci : 0 < c i) : f i ∈ F := by
  classical
  have hciF := (sum_mem_iff_mem hF (fun i => C.smul_mem (hc i) (hsC i))).mp hs i
  have hiF : ((c i)⁻¹ : R) • (c i • f i) ∈ F :=
    smul_mem (C := F) (x := (c i : R) • f i) (le_of_lt (Right.inv_pos.mpr hci)) hciF
  have hiF' := hiF
  rw [← smul_assoc] at hiF'
  have hiF'' : ((1 : R) • f i) ∈ F := by simpa [inv_mul_cancel₀ (ne_of_gt hci)] using hiF'
  simpa using hiF''

end IsFaceOf

end DivisionRing

section Ring

variable [Ring R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

namespace IsFaceOf

/-- The lineality space of a cone is a face. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  refine ⟨lineal_le C, ?_⟩
  intro x y a xC yC a0 hxy
  exact mem_lineal_of_smul_mem_lineal xC
    (lineal_isExtreme_left (C.smul_mem (le_of_lt a0) xC) yC hxy)

/-- The lineality space of a cone lies in every face. -/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F :=
  fun _ hx => hF.mem_of_add_mem hx.1 hx.2 (by simp)

/-- The lineality space of a face of a cone agrees with the lineality space of the cone. -/
lemma lineal_eq_lineal (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  constructor <;> intro ⟨hx, hx'⟩
  · exact ⟨hF.le hx, hF.le hx'⟩
  constructor
  · exact hF.mem_of_add_mem hx hx' (by simp)
  · exact hF.mem_of_add_mem hx' hx (by simp)

section Prod

variable [AddCommGroup N] [Module R N]

/-- The product of two faces of two cones is a face of the product of the cones. -/
theorem prod {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
    (hF₁ : F₁.IsFaceOf C₁) (hF₂ : F₂.IsFaceOf C₂) : IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := by
  constructor
  · intro x hx; simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩
  · simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, and_imp, Prod.forall]
    intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
    constructor
    · exact hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁
    · exact hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂

/-- The projection of a face of a product cone onto the first component is a face of the
  projection of the product cone onto the first component. -/
theorem fst {C₁ : PointedCone R M} {C₂ : PointedCone R N}
    {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.fst R M N)).IsFaceOf C₁ := by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩

/-- The projection of a face of a product cone onto the second component is a face of the
  projection of the product cone onto the second component. -/
theorem snd {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.snd R M N)).IsFaceOf C₂ := by
  have := map _ (LinearEquiv.prodComm R M N).injective hF
  convert fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end IsFaceOf

end Ring

end PointedCone




-- ################# PR end


namespace PointedCone

variable {R M N : Type*}


/-
  Cleanup for PR:
    - move Face stuff to Face/Lattice.lean
    - move lineal stuff to Face/Lineal.lean
    - move dual stuff to Face/Dual.lean
    * prove the priority stuff
    * prove sorry-s
    * replace span by linSpan
    * something else to add?
-/

-- NOTE: I think we should assume [Ring] from the start. There is little meaning for
-- working in a semiring ambient space.

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}


end Semiring

section DirectedOrderRing

variable [Ring R] [PartialOrder R] [IsDirectedOrder R] [IsOrderedRing R]
  [AddCommGroup M] [Module R M]
{C C₁ C₂ F F₁ F₂ : PointedCone R M}

lemma mem_linSpan_iff_mem (hF : F.IsFaceOf C) {x : M} (hx : x ∈ C) :
    x ∈ F.linSpan ↔ x ∈ F := by
  constructor <;> intro hxF
  · obtain ⟨_, hyF, _, hzF, rfl⟩ := (mem_linSpan F).1 hxF
    exact hF.mem_of_add_mem hx (hF.le hzF) hyF
  · exact Submodule.subset_span hxF

-- This fails for a merely partial order.
-- Let R = ℝ[X] with the coefficientwise order, M = R.
-- Let C be the cone of polynomials with all coefficients ≥ 0,
-- and F the face of nonnegative constant polynomials.
-- Then F is a face of C, but 1 ∈ F, so F.linSpan = ⊤.
-- Hence C ⊓ F.linSpan = C ≠ F.
lemma inf_linSpan (hF : F.IsFaceOf C) : C ⊓ F.linSpan = F := by
  apply le_antisymm <;> intro _ hx
  · exact (hF.mem_linSpan_iff_mem hx.1).mp hx.2
  · exact ⟨hF.le hx, Submodule.subset_span hx⟩

-- old proof
-- lemma inf_linSpan (hF : F.IsFaceOf C) : C ⊓ F.linSpan = F := by
--   apply le_antisymm
--   · intro x ⟨hxC, hxF⟩
--     obtain ⟨_, hyF, _, hzF, rfl⟩ := (mem_linSpan F).1 hxF
--     exact hF.mem_of_add_mem hxC (hF.le hzF) hyF
--   · simpa using ⟨hF.le, Submodule.subset_span⟩

end DirectedOrderRing
section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
{C C₁ C₂ F F₁ F₂ : PointedCone R M}

theorem salient {C F : PointedCone R M} (hC : C.Salient) (hF : F.IsFaceOf C) :
    F.Salient :=
  hC.anti hF.le

/-- Quotient by the linear span of a face is salient. -/
lemma salient_quot_linSpan_of_face [IsDirectedOrder R] (hF : F.IsFaceOf C) :
    (C.quot F.linSpan).Salient := by
  intro z hzC hz0 hzNeg
  rcases (PointedCone.mem_map).1 hzC with ⟨x, hxC, rfl⟩
  rcases (PointedCone.mem_map).1 hzNeg with ⟨y, hyC, hy⟩
  have hxySpan : x + y ∈ F.linSpan := by
    rw [← Submodule.ker_mkQ F.linSpan]
    exact LinearMap.mem_ker.mpr (by simp [map_add, hy])
  have hxyF : x + y ∈ F := by
    rw [← hF.inf_linSpan]
    exact ⟨C.add_mem hxC hyC, hxySpan⟩
  have hxF : x ∈ F := hF.mem_of_add_mem hxC hyC hxyF
  have hx0 : (F.linSpan).mkQ x = 0 := by
    simpa [Submodule.mkQ_apply] using
      (Submodule.Quotient.mk_eq_zero (p := F.linSpan) (x := x)).2
        (PointedCone.le_submodule_span F hxF)
  exact hz0 (by simpa using hx0)

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) : (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  inf h (refl _)


-- ## SUP

-- this is not the supremum we use in the face lattice. is it still interesting?

-- open Submodule in
-- private lemma uniq_decomp_of_zero_inter {xC xD yC yD : M}
--     (mxc : xC ∈ C₁) (myc : yC ∈ C₁) (mxd : xD ∈ C₂) (myd : yD ∈ C₂)
--     (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M))
--     (s : xC + xD = yC + yD) :
--     xC = yC ∧ xD = yD := by
--   -- sorry -- # broken since PR
--   let sub_mem_span {C x y} (mx : x ∈ C) (my : y ∈ C) : yC - xC ∈ span R C₁ :=
--     (PointedCone.span R C).sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
--   replace hCD := disjoint_def.mp hCD
--   constructor
--   · refine (sub_eq_zero.mp <| hCD _ (sub_mem_span mxc myc) ?_).symm
--     rw [add_comm] at s
--     rw [sub_eq_sub_iff_add_eq_add.mpr s.symm]
--     exact sub_mem_span myd mxd
--   · refine (sub_eq_zero.mp <| hCD _ ?_ (sub_mem_span mxd myd)).symm
--     nth_rewrite 2 [add_comm] at s
--     rw [← sub_eq_sub_iff_add_eq_add.mpr s]
--     exact sub_mem_span myc mxc

-- theorem sup_of_disjoint (hFC : F₁.IsFaceOf C₁) (hGD : F₂.IsFaceOf C₂)
--     (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M)) :
--     (F₁ ⊔ F₂).IsFaceOf (C₁ ⊔ C₂) := by
--   constructor
--   · simp only [sup_le_iff]
--     constructor
--     · apply le_trans _ le_sup_left
--       convert hFC.le
--     · apply le_trans _ le_sup_right
--       convert hGD.le
--   · intro x y a xs ys a0 h
--     simp only [mem_sup] at h xs ys ⊢
--     obtain ⟨xf, hxf, yg, hyg, hfg⟩ := h
--     obtain ⟨x', hx', y', hy', hfx⟩ := xs
--     obtain ⟨x'', hx'', y'', hy'', hfy⟩ := ys
--     have : (a • x' + x'') + (a • y' + y'') = xf + yg := by
--       rw [← hfy, ← hfx, smul_add] at hfg
--       simp [hfg]
--       abel
--     let mem {C : PointedCone R  M} {x y} (xCM yCM) : a • x + y ∈ C :=
--       C.add_mem (C.smul_mem (le_of_lt a0) xCM) yCM
--     have := uniq_decomp_of_zero_inter -- this requires Ring
--       (mem hx' hx'') (hFC.le hxf) (mem hy' hy'') (hGD.le hyg) hCD this
--     refine ⟨x', ?_, y', ?_, hfx⟩
--     · exact hFC.mem_of_smul_add_mem hx' hx'' a0 (by rwa [this.1])
--     · exact hGD.mem_of_smul_add_mem hy' hy'' a0 (by rwa [this.2])

-- theorem sup_of_disjoint_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂)
--     (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M))
--     : F.IsFaceOf (C₁ ⊔ C₂) := by
--   refine Eq.mp ?_ (sup_of_disjoint h₁ h₂ hCD)
--   simp

end Ring

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/-!
### Equivalent definition of isFaceOf on fields
-/

-- these now all follow kind of directly from mem_of_sum_smul_mem

-- lemma mem_of_sum_smul_mem'' {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
--     {c : ι → R} (hcc : ∀ i, 0 ≤ c i) (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, c i • f i ∈ F) (i : ι)
--     (cpos : 0 < c i) : f i ∈ F := by
--   -- sorry -- # broken since PR
--   exact mem_of_sum_smul_mem hF hsC hcc hs i cpos

-- -- ## PRIORITY
-- -- might not need field
-- -- prove this on semiring and follow non' version from it
-- lemma mem_of_sum_smul_mem' {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
--     (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, f i ∈ F) (i : ι) : f i ∈ F := by
--   refine mem_of_sum_smul_mem hF hsC (c := fun _ => 1) (fun i ↦ zero_le_one' R) (by simp [hs]) i ?_
--   exact zero_lt_one' R


lemma span_nonneg_lc_mem {ι : Type*} [Fintype ι] {c : ι → R} (hcc : ∀ i, 0 ≤ c i)
    {f : ι → s} {i : ι} (hF : F.IsFaceOf (span R s)) (h : ∑ i, c i • (f i).val ∈ F)
    (cpos : 0 < c i) : (f i).val ∈ F := by
  refine mem_of_sum_smul_mem hF ?_ hcc h i cpos
  simpa [mem_span] using fun i _ su => su (Subtype.coe_prop (f i))

-- lemma mem_of_sum_smul_memm {s : Finset M} (hF : F.IsFaceOf C) (hsC : (s : Set M) ⊆ C)
--     (hs : ∑ x ∈ s, x ∈ F) (x : M) (xs : x ∈ s) : x ∈ F := by
--   refine mem_of_sum_smul_mem
--     (f := fun (x : s) => x.val) hF ?_ (fun i ↦ zero_le_one' R) ?_ ⟨x, xs⟩ (zero_lt_one' R)
--   · exact (fun i => hsC i.property)
--   · simp only [Finset.univ_eq_attach, one_smul]
--     convert hs
--     exact s.sum_attach id

-- lemma iff_of_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₁) (h : F₂.IsFaceOf C) : F₂.IsFaceOf F₁ :=
--   ⟨_, fun h => (iff_le h h₁).mpr h₂⟩

-- section Map

-- variable [AddCommGroup N] [Module R N]

-- lemma comap_equiv (e : N ≃ₗ[R] M) (hF : F.IsFaceOf C) :
--     (PointedCone.comap (e : N →ₗ[R] M) F).IsFaceOf (.comap e C) :=
--   hF.comap e.surjective

-- end Map

/-!
### Intersections
-/

variable {s t : Set M}

lemma span_inter_face_span_inf_face (hF : F.IsFaceOf (span R s)) :
    span R (s ∩ F) = F := by
  ext x; constructor
  · simpa only [mem_span] using fun h => h F Set.inter_subset_right
  · intro h
    obtain ⟨n, c, g, xfg⟩ := mem_span_set'.mp (hF.le h)
    subst xfg
    apply sum_mem
    intro i _
    by_cases hh : 0 < c i
    · --sorry -- # broken since PR
      refine smul_mem _ (le_of_lt hh) ?_
      apply subset_span (E := M)
      exact Set.mem_inter (Subtype.coe_prop (g i)) (hF.span_nonneg_lc_mem (fun i => (c i).2) h hh)
    · push_neg at hh
      rw [le_antisymm hh (c i).property]
      simp

lemma exists_span_subset_face {s : Set M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t = F := ⟨_, Set.inter_subset_left, span_inter_face_span_inf_face hF⟩

-- If span R s and span R t are disjoint (only share 0)
example (h : span R s ⊓ span R t = ⊥)
    (hs : s ⊆ span R s) (ht : t ⊆ span R t) :
    span R (s ∩ t) = span R s ⊓ span R t := by
  -- When intersection is ⊥, both sides equal ⊥ if s ∩ t = ∅
  sorry


-- ## RESTRICT / EMBED

-- TODO: move to Faces lean file

lemma IsFaceOf.restrict (S : Submodule R M) (hF : F.IsFaceOf C) :
    (restrict S F).IsFaceOf (restrict S C) := ⟨restrict_mono S hF.1, hF.2⟩ -- hF.comap S.subtype

-- lemma IsFaceOf.embed {S : Submodule R M} {C F : PointedCone R S} (hF : F.IsFaceOf C) :
--     (embed F).IsFaceOf (embed C) := hF.map S.subtype_injective



-- ## QUOT / FIBER

abbrev IsFaceOf.quot {C F : PointedCone R M} (hF : F.IsFaceOf C) := C.quot (Submodule.span R F)

lemma quot {C F₁ F₂ : PointedCone R M} (hF₁ : F₁.IsFaceOf C) (hF₂ : F₂.IsFaceOf C)
    (hF : F₂ ≤ F₁) : (F₁.quot F₂.linSpan).IsFaceOf (C.quot F₂.linSpan) := by
  sorry

end DivisionRing



end IsFaceOf

end PointedCone
