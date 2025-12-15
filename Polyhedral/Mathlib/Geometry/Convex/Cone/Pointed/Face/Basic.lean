/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.Convex.Extreme

/-!
# Faces of pointed cones

This file defines the faces of a pointed cone and establishes some basic properties. A pointed cone
`F` is said to be a face of another pointed cone `C` if `F` is a subset of `C` and for every two
points in `C` a positive combination of whose is in `F`, the points also are in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We chose the definition that allows any positive combination of two points, instead of requiring
the sum of the points being in `F`. This definition is equivalent over fields, but more general over
rings.
* We prove that every face is an extreme set of its cone, but don't use `IsExtreme` as a definition,
since it is too restrictive. E.g. no subcone of the integer lattice could be considered a face then.

-/

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
structure IsFaceOf (F C : PointedCone R M) where
  le : F ≤ C
  left_mem_of_smul_add_mem :
    ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}

@[refl, simp]
theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun ⦃_⦄ a ↦ a, fun hx _ _ _ _ ↦ hx⟩

theorem rfl {C : PointedCone R M} : C.IsFaceOf C := refl C

theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  refine ⟨h₁.le.trans h₂.le, fun hx hy a0 b0 h ↦ ?_⟩
  refine h₁.2 (h₂.2 hx hy a0 b0 (h₁.le h)) ?_ a0 b0 h
  refine h₂.left_mem_of_smul_add_mem hy hx b0 a0 ?_
  rw [add_comm] at h
  exact h₁.le h

/- A face of a pointed cone is an extreme subset of the cone. -/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  refine ⟨h.le, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.left_mem_of_smul_add_mem xc yc a0 b0
  rwa [← hz] at zf

/- The infimum of two faces of two cones is a face of the infimum of the cones. -/
theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [Submodule.mem_inf, and_imp]
  intro x y a b xc₁ xc₂ yc₁ yc₂ a0 b0 hz₁ hz₂
  constructor
  · exact h₁.left_mem_of_smul_add_mem xc₁ yc₁ a0 b0 hz₁
  · exact h₂.left_mem_of_smul_add_mem xc₂ yc₂ a0 b0 hz₂

/- The infimum of two faces of a cone is again a face of the cone. -/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C := by
  refine Eq.mp ?_ (inf h₁ h₂)
  simp

theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) := by
  refine Eq.mp ?_ (inf h₁ h₂)
  simp

section Nontrivial

variable [NeZero (1 : R)]

lemma mem_of_add_mem (hF : F.IsFaceOf C) {x y : M}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x + y ∈ F) : x ∈ F := by
  simpa [hxy] using hF.left_mem_of_smul_add_mem hx hy zero_lt_one zero_lt_one

lemma iff_mem_of_smul_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ {x y : M} {c : R}, x ∈ C → y ∈ C → 0 < c → c • x + y ∈ F → x ∈ F := by
  constructor
  · intro f; refine ⟨f.le, ?_⟩
    intro x y c xC yC cpos h
    apply f.left_mem_of_smul_add_mem xC yC cpos zero_lt_one
    simp [h]
  · intro h
    constructor
    · exact h.1
    · intro x y a b xC yC a0 b0 hab
      exact h.2 xC (Submodule.smul_mem C ⟨_, le_of_lt b0⟩ yC) a0 hab

end Nontrivial

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/- An equivalent characterization of the faces of a pointed cone over a field: if the sum of two
points of the cone lies in a face, so do both summands. This is often used as the definition of a
face. -/
theorem iff_mem_of_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F := by
  constructor <;> intro h
  · exact ⟨h.le, mem_of_add_mem h⟩
  · apply iff_mem_of_smul_add_mem.mpr ⟨h.1, fun xC yC c0 hcxy => ?_⟩
    have cxF := h.2 (smul_mem _ (le_of_lt c0) xC) yC hcxy
    convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel _ (ne_of_lt c0).symm]

/- For any positive combination of points of a cone that is in a face, all the points are also in
the face. -/
theorem mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι → M} {c : ι → { c : R // 0 ≤ c }}
    (hF : F.IsFaceOf C) (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, c i • f i ∈ F) (i : ι)
    (cpos : 0 < c i) : f i ∈ F := by
  classical
  have := (Finset.univ (α:= ι)).add_sum_erase (a := i) (fun i : ι => c i • f i) (Finset.mem_univ _)
  simp_rw [← this] at hs
  convert smul_mem F (x := (c i : R) • f i) (le_of_lt (Right.inv_pos.mpr cpos)) _
  · rw [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel]
    · exact (MulAction.one_smul (f i)).symm
    · exact Ne.symm (ne_of_lt cpos)
  · refine (iff_mem_of_add_mem.mp hF).2 (C.smul_mem (le_of_lt cpos) (hsC i)) (sum_mem ?_) hs
    exact fun i a ↦ Submodule.smul_mem C (c i) (hsC i)

section Map

variable [AddCommGroup N] [Module R N]

/-- Mapping a face using an injective linear map yields a face of the image of `C`. -/
theorem iff_map {f : M →ₗ[R] N} (hf : Function.Injective f) :
     F.IsFaceOf C ↔ (PointedCone.map f F).IsFaceOf (.map f C) := by
  simp only [iff_mem_of_add_mem, mem_map, forall_exists_index, and_imp]
  constructor <;> intro ⟨sub, hF⟩
  · refine ⟨Submodule.map_mono sub, fun x xc xf _ yc yf _ _ h => ⟨x, hF xc yc ?_, xf⟩⟩
    rw [← xf, ← yf, ← f.map_add] at h
    rwa [← hf h]
  · refine ⟨fun x xf => ?_, fun hx hy hxy => ?_⟩
    · obtain ⟨y, yC, hy⟩ := Submodule.mem_map.mp <| sub (Submodule.mem_map_of_mem xf)
      rw [hf hy] at yC
      assumption
    · obtain ⟨x', hx', hx'f⟩ :=
        hF _ hx (Eq.refl _) _ hy (Eq.refl _) _ hxy (f.map_add _ _)
      rwa [hf hx'f] at hx'

/-- The preimage of a face under a surjective linear map is a face of the preimage of `C`. -/
theorem iff_comap {f : N →ₗ[R] M} (hf : Function.Surjective f) :
    F.IsFaceOf C ↔ (PointedCone.comap f F).IsFaceOf (.comap f C) := by
  simp only [iff_mem_of_add_mem, mem_comap, map_add]
  have ec (x : M) := Function.invFun_eq (hf x)
  constructor <;> intro ⟨sub, hF⟩
  · exact ⟨Submodule.comap_mono sub, hF⟩
  · constructor
    · intro x xF
      apply Submodule.map_le_iff_le_comap.mpr sub
      simp only [Submodule.mem_map, mem_comap, LinearMap.coe_restrictScalars]
      use Function.invFun f x
      rw [ec]
      exact ⟨xF, Eq.refl _⟩
    · intro x y xC yC h
      rw [← ec x] at h xC ⊢
      rw [← ec y] at h yC
      exact hF xC yC h
end Map

end Field

end IsFaceOf

end PointedCone














-- ################# PR end


namespace PointedCone

variable {R M N : Type*}



-- ## LINSPAN
-- copied this there so i don't need the dependency
section Semiring

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M] {S : Set M}

@[coe]
private abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

private instance : Coe (Submodule R M) (PointedCone R M) := ⟨Submodule.restrictScalars _⟩

/-- The linear span of the cone. -/
private abbrev linSpan (C : PointedCone R M) : Submodule R M := .span R C

end Semiring

/-
  Cleanup for PR:
    - move Face stuff to Face/Lattice.lean
    - move lineal stuff to Face/Lineal.lean
    - move dual stuff to Face/Dual.lean
    * prove the priority stuff
    * prove sorry-s
    * replace Submodule.span by linSpan
    * something else to add?
-/

-- NOTE: I think we should assume [Ring] from the start. There is little meaning for
-- working in a semiring ambient space.

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}


-- ## PRIORITY
lemma inf_linSpan (hF : F.IsFaceOf C) : C ⊓ F.linSpan = F := sorry

@[deprecated (since := "")]
alias inf_submodule := inf_linSpan

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) : (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  inf h rfl

end Semiring

-- ## SUP

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C C₁ C₂ F F₁ F₂ : PointedCone R M}

-- this is not the supremum we use in the face lattice. is it still interesting?

open Submodule in
private lemma uniq_decomp_of_zero_inter {xC xD yC yD : M}
    (mxc : xC ∈ C₁) (myc : yC ∈ C₁) (mxd : xD ∈ C₂) (myd : yD ∈ C₂)
    (hCD : Disjoint (Submodule.span R C₁) (Submodule.span (M := M) R C₂))
    (s : xC + xD = yC + yD) :
    xC = yC ∧ xD = yD := by
  let sub_mem_span {C x y} (mx : x ∈ C) (my : y ∈ C) :=
    (Submodule.span (M := M) R C).sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
  replace hCD := disjoint_def.mp hCD
  constructor
  · refine (sub_eq_zero.mp <| hCD _ (sub_mem_span mxc myc) ?_).symm
    rw [add_comm] at s
    rw [sub_eq_sub_iff_add_eq_add.mpr s.symm]
    exact sub_mem_span myd mxd
  · refine (sub_eq_zero.mp <| hCD _ ?_ (sub_mem_span mxd myd)).symm
    nth_rewrite 2 [add_comm] at s
    rw [← sub_eq_sub_iff_add_eq_add.mpr s]
    exact sub_mem_span myc mxc

theorem sup_of_disjoint (hFC : F₁.IsFaceOf C₁) (hGD : F₂.IsFaceOf C₂)
    (hCD : Disjoint (Submodule.span R C₁) (Submodule.span (M := M) R C₂)) :
    (F₁ ⊔ F₂).IsFaceOf (C₁ ⊔ C₂) := by
  constructor
  · simp only [sup_le_iff]
    constructor
    · apply le_trans _ le_sup_left
      convert hFC.le
    · apply le_trans _ le_sup_right
      convert hGD.le
  · intro _ _ a b xs ys a0 b0 h
    simp [Submodule.mem_sup] at h xs ys ⊢
    obtain ⟨xf, hxf, yg, hyg, hfg⟩ := h
    obtain ⟨x', hx', y', hy', hfx⟩ := xs
    obtain ⟨x'', hx'', y'', hy'', hfy⟩ := ys
    have : (a • x' + b • x'') + (a • y' + b • y'') = xf + yg := by
      rw [← hfy, ← hfx, smul_add] at hfg
      simp [hfg]
      abel
    let mem {C : PointedCone R  M} {x y} (xCM yCM) : a • x + b • y ∈ C :=
      C.add_mem (C.smul_mem (le_of_lt a0) xCM) (C.smul_mem (le_of_lt b0) yCM)
    have := uniq_decomp_of_zero_inter -- this requires Ring
      (mem hx' hx'') (hFC.le hxf) (mem hy' hy'') (hGD.le hyg) hCD this
    refine ⟨x', ?_, y', ?_, hfx⟩
    · exact hFC.left_mem_of_smul_add_mem hx' hx'' a0 b0 (by rwa [this.1])
    · exact hGD.left_mem_of_smul_add_mem hy' hy'' a0 b0 (by rwa [this.2])

theorem sup_of_disjoint_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂)
    (hCD : Disjoint (Submodule.span R C₁) (Submodule.span (M := M) R C₂))
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

-- these now all follow kind of directly from mem_of_sum_mem

lemma mem_of_sum_mem'' {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → M} (hF : F.IsFaceOf C)
    {c : ι → { c : R // 0 ≤ c }} (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, c i • f i ∈ F) (i : ι)
    (cpos : 0 < c i) : f i ∈ F := by
  exact mem_of_sum_mem hF hsC hs i cpos

-- ## PRIORITY
lemma mem_of_sum_mem' {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → M} (hF : F.IsFaceOf C)
    (hsC : ∀ i : ι, f i ∈ C) (hs : ∑ i : ι, f i ∈ F) (i : ι) : f i ∈ F := by
  refine mem_of_sum_mem hF hsC (c := fun _ => 1) (by simp [hs]) i ?_
  exact Subtype.mk_lt_mk.mpr (by norm_num)

lemma span_nonneg_lc_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ι → { c : R // 0 ≤ c }}
    {f : ι → s} {i : ι} (hF : F.IsFaceOf (span R s)) (h : ∑ i, c i • (f i).val ∈ F)
    (cpos : 0 < c i) : (f i).val ∈ F := by
  refine mem_of_sum_mem hF ?_ h i cpos
  simp [Submodule.mem_span]; exact fun i _ su => su (Subtype.coe_prop (f i))

lemma mem_of_sum_memm {s : Finset M} (hF : F.IsFaceOf C) (hsC : (s : Set M) ⊆ C)
    (hs : ∑ x ∈ s, x ∈ F) (x : M) (xs : x ∈ s) : x ∈ F := by
  refine mem_of_sum_mem (f := fun (x : s) => x.val) hF ?_ (c := fun _ => 1) ?_ ⟨x, xs⟩ ?_
  · exact (fun i => hsC i.property)
  · simp only [Finset.univ_eq_attach, one_smul]
    convert hs
    exact s.sum_attach id
  · exact Subtype.mk_lt_mk.mpr (by norm_num)

-- these only have one interesting direction, do we really need iff?

lemma iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  constructor
  · exact IsFaceOf.le
  · rw [iff_mem_of_smul_add_mem] at ⊢ h₁
    exact fun h => ⟨h, fun hx hy => h₁.2 (h₂.le hx) (h₂.le hy)⟩

lemma iff_of_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₁) :
    F₂.IsFaceOf C ↔ F₂.IsFaceOf F₁ :=
  ⟨fun h => (iff_le h h₁).mpr h₂, fun h => trans h h₁⟩

section Map

variable [AddCommGroup N] [Module R N]

-- ## MAP

-- o: not sure why we need extra lemmas for these

lemma map {f : M →ₗ[R] N} (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (map f F).IsFaceOf (map f C) := (iff_map hf).mp hF

lemma map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (PointedCone.map (e : M →ₗ[R] N) F).IsFaceOf (.map e C) := hF.map e.injective

lemma comap {f : N →ₗ[R] M} (hf : Function.Surjective f) (hF : F.IsFaceOf C) :
    (comap f F).IsFaceOf (comap f C) := (iff_comap hf).mp hF

lemma comap_equiv (e : N ≃ₗ[R] M) (hF : F.IsFaceOf C) :
    (PointedCone.comap (e : N →ₗ[R] M) F).IsFaceOf (.comap e C) := hF.comap e.surjective

end Map

/-!
### Intersections
-/

variable {s t : Set M}

lemma span_inter_face_span_inf_face (hF : F.IsFaceOf (span R s)) :
    span R (s ∩ F) = F := by
  ext x; constructor
  · simp [Submodule.mem_span]
    exact fun h => h F Set.inter_subset_right
  · intro h
    obtain ⟨n, c, g, xfg⟩ := Submodule.mem_span_set'.mp (hF.le h)
    subst xfg
    apply Submodule.sum_mem
    intro i _
    by_cases hh : 0 < c i
    · apply Submodule.smul_mem; apply Submodule.subset_span
      refine Set.mem_inter (Subtype.coe_prop (g i)) (hF.span_nonneg_lc_mem h hh)
    · push_neg at hh
      rw [le_antisymm hh (c i).property]
      simp

lemma exists_span_subset_face {s : Set M} (hF : F.IsFaceOf (span R s)) :
    ∃ t ⊆ s, span R t = F := ⟨_, Set.inter_subset_left, span_inter_face_span_inf_face hF⟩

-- If span R s and span R t are disjoint (only share 0)
example (h : Submodule.span R s ⊓ Submodule.span R t = ⊥)
    (hs : s ⊆ Submodule.span R s) (ht : t ⊆ Submodule.span R t) :
    Submodule.span R (s ∩ t) = Submodule.span R s ⊓ Submodule.span R t := by
  -- When intersection is ⊥, both sides equal ⊥ if s ∩ t = ∅
  sorry

end Field

end IsFaceOf

end PointedCone
