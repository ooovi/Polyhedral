/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/

import Mathlib.Analysis.Convex.Extreme

import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Lineal

open Submodule

/-!
# Faces of pointed cones

This file defines the faces of a pointed cone and establishes some basic properties. A pointed cone
`F` is said to be a face of a pointed cone `C` if `F` is a subset of `C` and for every two
points in `C` a positive combination of whose is in `F`, the points are also in `F`.

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
structure IsFaceOf (F C : PointedCone R M) where
  le : F ≤ C
  mem_of_smul_add_mem :
    ∀ {x y : M} {a : R}, x ∈ C → y ∈ C → 0 < a → a • x + y ∈ F → x ∈ F

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

/-- A pointed cone `C` as a face of itself. -/
@[refl, simp]
theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

theorem iff_mem_of_smul_add_smul_mem : F.IsFaceOf C ↔
    F ≤ C ∧ ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F := by
  constructor <;> intro h
  · refine ⟨h.1, fun xC yC a0 b0 hab => ?_⟩
    exact h.2 xC (Submodule.smul_mem C ⟨_, le_of_lt b0⟩ yC) a0 hab
  · refine ⟨h.1, ?_⟩
    by_cases hc : 0 < (1 : R)
    · intros xc yc a0 haxy
      exact h.2 xc yc a0 hc (by simpa)
    · simp [(subsingleton_of_zero_eq_one (zero_le_one.eq_or_lt.resolve_right hc)).eq_zero]

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  rw [iff_mem_of_smul_add_smul_mem] at h₁ h₂ ⊢
  refine ⟨h₁.1.trans h₂.1, fun hx hy a0 b0 h ↦ ?_⟩
  exact h₁.2 (h₂.2 hx hy a0 b0 (h₁.1 h)) (h₂.2 hy hx b0 a0 (by rw [add_comm]; exact h₁.1 h)) a0 b0 h

/-- Two faces of a cone are contained in each other if and only if one is a face of the other. -/
theorem iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂:= by
  constructor <;> intro h
  · exact h.le
  rw [iff_mem_of_smul_add_smul_mem] at ⊢ h₁
  exact ⟨h, fun hx hy => h₁.2 (h₂.le hx) (h₂.le hy)⟩

/- A face of a cone is an extreme subset of the cone. -/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  apply iff_mem_of_smul_add_smul_mem.mp at h
  refine ⟨h.1, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.2 xc yc a0 b0
  rwa [← hz] at zf

/- The intersection of two faces of two cones is a face of the intersection of the cones. -/
theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

/- The intersection of two faces of a cone is a face of the cone. -/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  inf_idem C ▸ inf h₁ h₂

/- If a cone is a face of two cones simultaneously, then it is also a face of their intersection. -/
theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) :=
  inf_idem F ▸ inf h₁ h₂

theorem mem_of_add_mem (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : x ∈ F := by
  by_cases hc : 0 < (1 : R)
  · simpa [hxy] using hF.mem_of_smul_add_mem hx hy hc
  · have := subsingleton_of_zero_eq_one (zero_le_one.eq_or_lt.resolve_right hc)
    have := Module.subsingleton R M
    simp [this.eq_zero]

theorem mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, f i ∈ F) (i : ι) : f i ∈ F := by
  classical
  refine hF.mem_of_add_mem (hsC i) (sum_mem (fun j (_ : j ∈ Finset.univ.erase i) => hsC j)) ?_
  simp [hs]

section Map

variable [AddCommGroup N] [Module R N]

/-- The image of a face of a cone under an injective linear map is a face of the
  image of the cone. -/
theorem map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
     F.IsFaceOf C ↔ (F.map f).IsFaceOf (C.map f) := by
  constructor <;> intro ⟨sub, hF⟩
  · refine ⟨map_mono sub, ?_⟩
    simp only [mem_map, forall_exists_index, and_imp]
    intro _ _ a b bC fbx _ cC fcy ha _ x'F h
    refine ⟨b, ⟨?_, fbx⟩⟩
    apply hF bC cC ha
    convert x'F
    apply hf
    simp [h, fbx, fcy]
  · refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
    · obtain ⟨y, yC, hy⟩ := mem_map.mp <| sub (mem_map_of_mem xf)
      rwa [hf hy] at yC
    · simp only [mem_map, forall_exists_index, and_imp] at hF
      obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
      convert hx'
      exact hf hhx'.symm

/-- The image of a face of a cone under an injective linear map is a face of the
  image of the cone. -/
theorem map {f : M →ₗ[R] N} (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (F.map f).IsFaceOf (C.map f) := (map_iff hf).mp hF

/-- The image of a face of a cone under an equivalence is a face of the image of the cone. -/
theorem map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) := hF.map e.injective

/-- The comap of a face of a cone under a linear map is a face of the comap of the cone. -/
theorem comap {f : N →ₗ[R] M} (hF : F.IsFaceOf C) :
    (F.comap f).IsFaceOf (C.comap f) := by
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

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

theorem iff_mem_of_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F := by
  constructor <;> intro h
  · exact ⟨h.le, mem_of_add_mem h⟩
  · refine ⟨h.1, fun xC yC c0 hcxy => ?_⟩
    have cxF := h.2 (smul_mem _ (le_of_lt c0) xC) yC hcxy
    convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel _ (ne_of_lt c0).symm]

/- If the positive combination of points of a cone is in a face, then all the points are
  in the face. -/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → R}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i : ι, c i • f i ∈ F)
    (i : ι) (hci : 0 < c i) : f i ∈ F := by
  classical
  have := mem_of_sum_mem hF (fun i => C.smul_mem (hc i) (hsC i)) hs i
  convert smul_mem (C := F) (x := (c i : R) • f i) (le_of_lt (Right.inv_pos.mpr hci)) this
  rw [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel]
  · exact (MulAction.one_smul (f i)).symm
  · exact Ne.symm (ne_of_lt hci)

theorem mem_of_sum_smul_mem''' {s : Finset M} {c : M → R}
    (hF : F.IsFaceOf C) (hsC : ∀ x ∈ s, x ∈ C) (hc : ∀ x ∈ s, 0 ≤ c x) (hs : ∑ x ∈ s, c x • x ∈ F)
    (x : M) (hx : x ∈ s) (hci : 0 < c x) : x ∈ F := by sorry

/-- The lineality space of a cone is a face. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  rw [iff_mem_of_add_mem]
  simp only [lineal_le, true_and]
  intro _ _ xc yc xyf
  sorry -- broken since PR
  -- simp [neg_add_rev, xc, true_and] at xyf ⊢
  -- simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

/-- The lineality space of a cone lies in every face. -/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal ≤ F := sorry -- broken since PR
  -- fun _ hx => hF.mem_of_add_mem hx.1 hx.2 (by simp)

/-- The lineality space of a face of a cone agrees with the lineality space of the cone. -/
lemma lineal_eq_lineal (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  sorry -- broken since PR
  -- constructor <;> intro ⟨hx, hx'⟩
  -- · exact ⟨hF.le hx, hF.le hx'⟩
  -- constructor
  -- · exact hF.mem_of_add_mem hx hx' (by simp)
  -- · exact hF.mem_of_add_mem hx' hx (by simp)

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
  have := map (LinearEquiv.prodComm R M N).injective hF
  convert fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end Field

end IsFaceOf

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

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}


-- ## PRIORITY
-- this is false without a linear order: consider ℝ with the trivial ordering
-- (i.e., only elements in ℤ are comparable) then C:= ℕ + √2 ℕ is and ℕ ⊆ ℂ a face,
-- but ℤ.linSpan ∩ C = C
lemma inf_linSpan (hF : F.IsFaceOf C) : C ⊓ F.linSpan = F := by
  apply le_antisymm
  · intro x ⟨xC, xF⟩
    have : ∃ p ∈ F, ∃ n ∈ F, p = x + n := by sorry -- (mem_linSpan F).1 this
    rcases this with ⟨p, pf, n, nf, rfl⟩
    exact hF.mem_of_add_mem xC (hF.le nf) pf
  · exact le_inf_iff.mpr ⟨hF.le, le_submodule_span_of_le fun ⦃x⦄ a ↦ a⟩



@[deprecated (since := "")]
alias inf_submodule := inf_linSpan

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) : (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  inf h (refl _)

end Semiring

-- ## SUP

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C C₁ C₂ F F₁ F₂ : PointedCone R M}

-- this is not the supremum we use in the face lattice. is it still interesting?

open Submodule in
private lemma uniq_decomp_of_zero_inter {xC xD yC yD : M}
    (mxc : xC ∈ C₁) (myc : yC ∈ C₁) (mxd : xD ∈ C₂) (myd : yD ∈ C₂)
    (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M))
    (s : xC + xD = yC + yD) :
    xC = yC ∧ xD = yD := by
  sorry -- # broken since PR
  -- let sub_mem_span {C x y} (mx : x ∈ C) (my : y ∈ C) :=
  --   (span (M := M) R C).sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
  -- replace hCD := disjoint_def.mp hCD
  -- constructor
  -- · refine (sub_eq_zero.mp <| hCD _ (sub_mem_span mxc myc) ?_).symm
  --   rw [add_comm] at s
  --   rw [sub_eq_sub_iff_add_eq_add.mpr s.symm]
  --   exact sub_mem_span myd mxd
  -- · refine (sub_eq_zero.mp <| hCD _ ?_ (sub_mem_span mxd myd)).symm
  --   nth_rewrite 2 [add_comm] at s
  --   rw [← sub_eq_sub_iff_add_eq_add.mpr s]
  --   exact sub_mem_span myc mxc

theorem sup_of_disjoint (hFC : F₁.IsFaceOf C₁) (hGD : F₂.IsFaceOf C₂)
    (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M)) :
    (F₁ ⊔ F₂).IsFaceOf (C₁ ⊔ C₂) := by
  sorry -- # broken since PR
  -- constructor
  -- · simp only [sup_le_iff]
  --   constructor
  --   · apply le_trans _ le_sup_left
  --     convert hFC.le
  --   · apply le_trans _ le_sup_right
  --     convert hGD.le
  -- · intro _ _ a b xs ys a0 b0 h
  --   simp [mem_sup] at h xs ys ⊢
  --   obtain ⟨xf, hxf, yg, hyg, hfg⟩ := h
  --   obtain ⟨x', hx', y', hy', hfx⟩ := xs
  --   obtain ⟨x'', hx'', y'', hy'', hfy⟩ := ys
  --   have : (a • x' + b • x'') + (a • y' + b • y'') = xf + yg := by
  --     rw [← hfy, ← hfx, smul_add] at hfg
  --     simp [hfg]
  --     abel
  --   let mem {C : PointedCone R  M} {x y} (xCM yCM) : a • x + b • y ∈ C :=
  --     C.add_mem (C.smul_mem (le_of_lt a0) xCM) (C.smul_mem (le_of_lt b0) yCM)
  --   have := uniq_decomp_of_zero_inter -- this requires Ring
  --     (mem hx' hx'') (hFC.le hxf) (mem hy' hy'') (hGD.le hyg) hCD this
  --   refine ⟨x', ?_, y', ?_, hfx⟩
  --   · exact hFC.mem_of_smul_add_mem hx' hx'' a0 b0 (by rwa [this.1])
  --   · exact hGD.mem_of_smul_add_mem hy' hy'' a0 b0 (by rwa [this.2])

theorem sup_of_disjoint_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂)
    (hCD : Disjoint (span R C₁) (span R C₂ : PointedCone R M))
    : F.IsFaceOf (C₁ ⊔ C₂) := by
  refine Eq.mp ?_ (sup_of_disjoint h₁ h₂ hCD)
  simp

end Ring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/-!
### Equivalent definition of isFaceOf on fields
-/

-- these now all follow kind of directly from mem_of_sum_smul_mem

lemma mem_of_sum_smul_mem'' {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → M} (hF : F.IsFaceOf C)
    {c : ι → R} (hcc : ∀ i, 0 ≤ c i) (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, c i • f i ∈ F) (i : ι)
    (cpos : 0 < c i) : f i ∈ F := by
  sorry -- # broken since PR
  -- exact mem_of_sum_smul_mem hcc hF hsC hs i cpos

-- ## PRIORITY
-- might not need field
-- prove this on semiring and follow non' version from it
lemma mem_of_sum_smul_mem' {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, f i ∈ F) (i : ι) : f i ∈ F := by
  sorry -- # broken since PR
  -- refine mem_of_sum_smul_mem (fun i ↦ zero_le_one' R) hF hsC (c := fun _ => 1) (by simp [hs]) i ?_
  -- exact Subtype.mk_lt_mk.mpr (by norm_num)


lemma span_nonneg_lc_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → R} (hcc : ∀ i, 0 ≤ c i)
    {f : ι → s} {i : ι} (hF : F.IsFaceOf (span R s)) (h : ∑ i, c i • (f i).val ∈ F)
    (cpos : 0 < c i) : (f i).val ∈ F := by
  sorry -- # broken since PR
  -- refine mem_of_sum_smul_mem hcc hF ?_ h i cpos
  -- simp [mem_span]; exact fun i _ su => su (Subtype.coe_prop (f i))

lemma mem_of_sum_smul_memm {s : Finset M} (hF : F.IsFaceOf C) (hsC : (s : Set M) ⊆ C)
    (hs : ∑ x ∈ s, x ∈ F) (x : M) (xs : x ∈ s) : x ∈ F := by
  sorry -- # broken since PR
  -- refine mem_of_sum_smul_mem
  --   (f := fun (x : s) => x.val) (fun i ↦ zero_le_one' R) hF ?_ ?_ ⟨x, xs⟩ (zero_lt_one' R)
  -- · exact (fun i => hsC i.property)
  -- · simp only [Finset.univ_eq_attach, one_smul]
  --   convert hs
  --   exact s.sum_attach id

lemma iff_of_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₁) (h : F₂.IsFaceOf C) : F₂.IsFaceOf F₁ :=
  sorry -- # broken since PR
  -- fun h => (iff_le h h₁).mpr h₂

section Map

variable [AddCommGroup N] [Module R N]

lemma comap_equiv (e : N ≃ₗ[R] M) (hF : F.IsFaceOf C) :
    (PointedCone.comap (e : N →ₗ[R] M) F).IsFaceOf (.comap e C) := sorry -- # broken since PR
  -- hF.comap e.surjective

end Map

/-!
### Intersections
-/

variable {s t : Set M}

lemma span_inter_face_span_inf_face (hF : F.IsFaceOf (span R s)) :
    span R (s ∩ F) = F := by
  ext x; constructor
  · simp [mem_span]
    exact fun h => h F Set.inter_subset_right
  · intro h
    obtain ⟨n, c, g, xfg⟩ := mem_span_set'.mp (hF.le h)
    subst xfg
    apply sum_mem
    intro i _
    by_cases hh : 0 < c i
    · sorry -- # broken since PR
      -- apply smul_mem
      -- apply subset_span
      -- refine Set.mem_inter (Subtype.coe_prop (g i)) (hF.span_nonneg_lc_mem h hh)
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

end Field

end IsFaceOf

end PointedCone
