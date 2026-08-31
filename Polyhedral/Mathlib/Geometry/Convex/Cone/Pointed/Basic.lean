/-
Copyright (c) 2025 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.RingTheory.LocalRing.Basic

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic
import Polyhedral.Mathlib.Algebra.Order.Nonneg.Basic

/-! This file proves basic facts about cones that are intended to go into Pointed/Basic. -/

namespace PointedCone

open Pointwise

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

local notation "R≥0" => Nonneg R

instance : Algebra R≥0 R where
  algebraMap := Nonneg.coeRingHom
  commutes' r x := mul_comm ..
  smul_def' r x := by aesop

end CommSemiring

section Semiring

open Module Function
open Submodule (span)

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- allows us to use dot notation for lemmas in Submodule.FG or PointedCone.FG
abbrev FG (C : PointedCone R M) : Prop := Submodule.FG C

-- ## COE

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf _ _ _

lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  Submodule.restrictScalars_sInf _ _

lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M)
    := Submodule.restrictScalars_sup _ _ _

lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  Submodule.restrictScalars_sSup _ _

lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]

-- ## HULL

lemma le_hull {s : Set M} : s ≤ hull R s := Submodule.subset_span

lemma hull_hull {s : Set M} : hull R (hull R s) = hull R s := Submodule.span_span

lemma hull_eq {S : PointedCone R M} : hull R S = S := Submodule.span_eq S

lemma hull_mono {s t : Set M} (h : s ⊆ t) : hull R s ≤ hull R t := Submodule.span_mono h

lemma hull_monotone : Monotone (hull R : Set M → PointedCone R M) :=
  fun _ _ => hull_mono

def hull_gi : GaloisInsertion (hull R : Set M → PointedCone R M) (↑) where
  choice s _ := hull R s
  gc _ _ := Submodule.span_le
  le_l_u _ := subset_hull
  choice_eq _ _ := rfl

@[simp] lemma span_hull_eq_submodule_span (s : Set M) :
    span R (hull R s) = span R s := Submodule.span_span_of_tower ..

-- TODO: this is only needed because `Submodule.span_insert` is restricted to rings
lemma hull_insert (x) (s : Set M) : hull R (insert x s) = hull R {x} ⊔ hull R s :=
  Submodule.span_insert x s

lemma coe_sup_submodule_span' {s t : Set M} :
    Submodule.span R (s ∪ t) = Submodule.span R (hull R s ⊔ hull R t) := by simp

-- Has this anything to do with cones? See version above
lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ∪ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  rw [← span_hull_eq_submodule_span]
  simp [Submodule.span_union]

lemma hull_le_submodule_span (s : Set M) : hull R s ≤ Submodule.span R s :=
    Submodule.span_le_restrictScalars _ _ s

lemma le_span {C : PointedCone R M} : C ≤ span R (C : Set M) := Submodule.subset_span

lemma hull_union (s t : Set M) : hull R (s ∪ t) = hull R s ⊔ hull R t :=
  Submodule.span_union s t

lemma sup_eq_hull_union (C D : PointedCone R M) : C ⊔ D = hull R (C ∪ D) := by
  rw [← hull_eq (S := C), ← hull_eq (S := D), hull_union]
  simp

lemma sSup_eq_hull_iUnion (S : Set (PointedCone R M)) :
    sSup S = hull R (sSup (SetLike.coe '' S)) := by
  apply le_antisymm
  · refine sSup_le fun C hC _ hx => ?_
    have : (C : Set M) ∈ SetLike.coe '' S := ⟨C, hC, rfl⟩
    exact le_hull <| (le_sSup this) hx
  · refine Submodule.span_le.mpr fun x hx => ?_
    rw [Set.sSup_eq_sUnion] at hx
    obtain ⟨_, ⟨_, hC, rfl⟩, hx⟩ := hx
    exact (le_sSup hC) hx

end Semiring

section Ring

open Submodule (span)

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- TODO: write version with `restrictScalars` instead. (Or is there already one?)
lemma sup_inf_submodule_span_of_disjoint {C : PointedCone R M} {S : Submodule R M}
  (hS : Disjoint (span R C) S) : (C ⊔ S) ⊓ span R (C : Set M) = C := by
  rw [sup_inf_assoc_of_le_submodule]
  · rw [inf_comm, ← coe_inf, disjoint_iff.mp hS]; simp
  · exact Submodule.subset_span

end Ring

section AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simps!]
def linealCone (C : PointedCone R M) : PointedCone R M where
  __ := C.support
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · by_contra; exact hr r.2

end AddCommGroup

section Ring

section PartialOrder

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simp] lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by
  ext x; simp

lemma hull_neg (s : Set M) : hull R (-s) = - hull R s := by
  rw [hull, Submodule.span_neg_eq_neg]

lemma map_id_eq_neg (C : PointedCone R M) : C.map (-.id) = -C := by
  ext x
  simp only [Submodule.mem_neg, mem_map, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
  constructor
  · intro h
    obtain ⟨y, hyC, rfl⟩ := h
    simpa using hyC
  · exact fun h => by use -x; simp [h]

lemma comap_id_eq_neg (C : PointedCone R M) : C.comap (-.id) = -C := by
  ext x; simp

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma map_neg (C : PointedCone R M) (f : M →ₗ[R] N) : map (-f) C = map f (-C) := by
  ext x
  simp only [mem_map, LinearMap.neg_apply, Submodule.mem_neg]
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨-x, by simpa using hx⟩
  }

lemma map_neg_apply (C : PointedCone R M) (f : M →ₗ[R] N) : - map f C = map f (-C) := by
  ext x
  simp only [Submodule.mem_neg, mem_map]
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨-x, by simpa [neg_eq_iff_eq_neg] using hx⟩
  }

lemma comap_neg (C : PointedCone R M) (f : N →ₗ[R] M) : comap (-f) C = comap f (-C) := by
  ext x; simp

lemma comap_neg_apply (C : PointedCone R M) (f : N →ₗ[R] M) : -comap f C = comap f (-C) := by
  ext x; simp

end PartialOrder

section DirectedOrderRing

/- NOTE: This section is mathlib PR #36605. Delete it after PR is merged. -/

open Submodule

variable {R : Type*} [Ring R] [PartialOrder R] [IsDirectedOrder R] [IsOrderedRing R]
variable {E : Type*} [AddCommGroup E] [Module R E]

variable {C : PointedCone R E} {x : E}

/-- A cone that is closed under negation forms a submodule. -/
abbrev toSubmodule (hC : -C = C) : Submodule R E where
  __ := C
  smul_mem' a x hx := by
    obtain ⟨b, hab, hb⟩ := exists_ge_ge a 0
    suffices b • x + -(b - a) • x ∈ C by
      rw [← add_smul] at this
      abel_nf at this
      exact this
    have : -(b - a) • x ∈ C := by
      rw [← hC]
      simpa [← neg_smul] using smul_mem _ (sub_nonneg.mpr hab) hx
    aesop

@[simp] lemma ofSubmodule_toSubmodule (hC : -C = C) : C.toSubmodule hC = C := rfl

lemma coe_toSubmodule (hC : -C = C) : (C.toSubmodule hC : Set E) = C := by simp

lemma mem_toSubmodule {hC : -C = C} : x ∈ C.toSubmodule hC ↔ x ∈ C := by simp

instance : CanLift (PointedCone R E) (Submodule R E) ofSubmodule (fun C => -C = C) where
  prf _ h := ⟨toSubmodule h, ofSubmodule_toSubmodule h⟩

variable (R)

lemma span_eq_hull_neg_sup_hull (s : Set E) : span R s = hull R (-s) ⊔ hull R s := by
  suffices span R s = (hull R (-s) ⊔ hull R s).toSubmodule
    (by simp [← span_neg_eq_neg, sup_comm]) by simp [this]
  refine span_eq_of_le _ (fun x hx ↦ ?_) ?_
  · simpa using mem_sup_right (Submodule.subset_span hx)
  · rw [← ofSubmodule_le_ofSubmodule]
    simpa [hull_le_span] using hull_le_span R (-s)

variable (x) in
@[simp] lemma hull_neg_pair_eq_span_singleton : hull R {-x, x} = R ∙ x := by
  change hull R ({-x} ∪ {x}) = (R ∙ x)
  simp only [span_union, span_eq_hull_neg_sup_hull, Set.neg_singleton]

lemma hull_eq_span_of_neg_eq {s : Set E} (hs : -s = s) :
    hull R s = span R s := by
  simp [span_eq_hull_neg_sup_hull, hs]

variable {R}

variable (C) in
lemma span_eq_neg_sup : span R (C : Set E) = -C ⊔ C := by
  simp [span_eq_hull_neg_sup_hull, span_neg_eq_neg]

lemma mem_span_iff_mem_neg_sup : x ∈ span R C ↔ x ∈ -C ⊔ C := by
  rw [← span_eq_neg_sup, mem_ofSubmodule_iff]

lemma mem_span : x ∈ span R C ↔ ∃ p ∈ C, ∃ n ∈ C, x = p - n := by
  simp_rw [mem_span_iff_mem_neg_sup, mem_sup, mem_neg]
  refine ⟨fun ⟨y, hy', z, hz, h⟩ ↦ ?_, fun ⟨p, hp, n, hn, h⟩ ↦ ?_⟩
  · exact ⟨z, hz, -y, hy', by grind⟩
  · exact ⟨-n, by simp [hn], x + n, by simp [h, hp], by simp⟩

end DirectedOrderRing

section PartialOrder

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- This lemma is used in Faces/Basic.lean. It should probably be moved there.
open Submodule in
lemma uniq_decomp_of_zero_inter {C D : PointedCone R M} {xC xD yC yD : M}
    (mxc : xC ∈ C) (myc : yC ∈ C) (mxd : xD ∈ D) (myd : yD ∈ D)
    (hCD : Disjoint (span R (C : Set M)) (span R D))
    (s : xC + xD = yC + yD) :
    xC = yC ∧ xD = yD := by
  let sub_mem_span {C : PointedCone R M} {x y} (mx : x ∈ C) (my : y ∈ C) :=
    (span R (C : Set M)).sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
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

end PartialOrder

section LinearOrder

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_hull (f : M →ₗ[R] M') (s : Set M) : map f (hull R s) = hull R (f '' s) :=
  Submodule.map_span _ _

end Map

end LinearOrder

end Ring

-- # QUOTIENTS

/- Most, if not everything, from this section should be proven for general restricted scalars. -/

section Quotient

open Submodule (span)

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

variable {C : PointedCone R M}

/-- The quotient of a cone along a submodule. -/
abbrev quot (C : PointedCone R M) (S : Submodule R M) : PointedCone R (M ⧸ S) := C.map S.mkQ

lemma quot_def (C : PointedCone R M) (S : Submodule R M) : C.quot S = C.map S.mkQ := rfl

lemma quot_eq_bot_iff (C : PointedCone R M) (S : Submodule R M) :
    C.quot S = ⊥ ↔ C ≤ S := by
  simp only [quot, PointedCone.ext_iff, PointedCone.map]
  constructor
  · intro h x hx
    exact (Submodule.Quotient.mk_eq_zero _).mp <| (h (S.mkQ x)).mp ⟨x, hx, rfl⟩
  · intro h y
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mkQ_apply,
      Submodule.mem_bot]
    constructor
    · rintro ⟨y₁, hy₁, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero S).mpr (h hy₁)
    · rintro rfl
      exact ⟨0, C.zero_mem, Submodule.Quotient.mk_zero S⟩

lemma quot_bot_of_le {S : Submodule R M} (h : C ≤ S) : C.quot S = ⊥ := (quot_eq_bot_iff C S).mpr h

lemma quot_span : C.quot (.span R C) = ⊥ := quot_bot_of_le Submodule.le_span

lemma quot_fg (hC : C.FG) (S : Submodule R M) : (C.quot S).FG := hC.map _

/-- The span of a quotient cone is the image of the span under the quotient map. -/
@[simp] lemma span_quot (C : PointedCone R M) (S : Submodule R M) :
    span R (C.quot S) = Submodule.map S.mkQ (span R C) := by
  simp [PointedCone.quot]

@[simp] lemma sup_quot_eq_quot (C : PointedCone R M) (S : Submodule R M) :
    (C ⊔ S).quot S = C.quot S :=
  Submodule.map_mkQ_eq_iff_sup_eq.mpr (by simp)

@[simp]
lemma quot_eq_iff_sup_eq {S : Submodule R M} {C D : PointedCone R M} :
    C.quot S = D.quot S ↔ C ⊔ S = D ⊔ S := Submodule.map_mkQ_eq_iff_sup_eq

@[simp] lemma map_mkQ_le_iff_sup_le {p : Submodule R M} {s t : PointedCone R M} :
    map p.mkQ s ≤ map p.mkQ t ↔ s ⊔ p ≤ t ⊔ p := Submodule.map_mkQ_le_iff_sup_le

@[simp] lemma map_mkQ_eq_iff_sup_eq {p : Submodule R M} {s t : PointedCone R M} :
    map p.mkQ s = map p.mkQ t ↔ s ⊔ p = t ⊔ p := Submodule.map_mkQ_eq_iff_sup_eq

section CommRing

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

local notation "R≥0" => {c : R // 0 ≤ c}

noncomputable def IsCompl.map_mkQ_equiv_inf {S T : Submodule R M} (hST : IsCompl S T)
    {C : PointedCone R M} (hSC : S ≤ C) : C.quot S ≃ₗ[R≥0] (C ⊓ T : PointedCone R M) :=
  Submodule.IsCompl.map_mkQ_equiv_inf hST hSC

end CommRing

end Quotient

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- analogue of `Submodule.span_singleton_smul_eq`
theorem hull_singleton_smul_eq {r : R} (hr : r > 0) (x : M) : R ∙₊ (r • x) = R ∙₊ x := by
  ext y
  simp only [Submodule.mem_span_singleton, Subtype.exists, Nonneg.mk_smul, exists_prop]
  constructor <;> intro h <;> obtain ⟨a, ha, h⟩ := h
  · use a * r
    constructor
    · exact mul_nonneg ha (le_of_lt hr)
    · simpa [smul_smul] using h
  · use a * r⁻¹
    constructor
    · exact mul_nonneg ha (le_of_lt (inv_pos.mpr hr))
    · simpa [smul_smul, inv_mul_cancel_right₀ (ne_of_lt hr).symm] using h

end DivisionRing

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

open Set

/-- If there is a linear map that is positive on the entire cone except 0, the cone is the sMul-span
of any positive level set of the map. -/
lemma eq_Ioi_zero_smul_inter_preimage_of_pos {C : PointedCone R M} {f : M →ₗ[R] R} {r : R}
    (hf : ∀ x ∈ C, x ≠ 0 → 0 < f x) (hr : 0 < r) :
    (C : Set M) \ {0} = Set.Ioi (0 : R) • ((C : Set M) ∩ f ⁻¹' {r}) := by
  ext x
  constructor
  · intro ⟨hxC, hx0⟩
    refine ⟨r⁻¹ • f x, smul_pos (inv_pos.mpr hr) <| hf x hxC hx0, (r • (f x)⁻¹) • x, ⟨?_, ?_⟩, ?_⟩
    · exact C.smul_mem (smul_pos hr <| inv_pos.mpr (hf _ hxC hx0)).le hxC
    · simp [inv_mul_cancel₀ (ne_of_gt (hf x hxC hx0)), mul_assoc]
    · simp only [smul_eq_mul, smul_smul]
      field_simp [ne_of_gt (hf x hxC hx0)]
      exact MulAction.one_smul x
  · rintro ⟨r, hri, y, ⟨hyC, hfy⟩, rfl⟩
    have hy0 : y ≠ 0 := by intro hc; simp only [hc, mem_preimage, map_zero,
      Set.mem_singleton_iff] at hfy; exact hr.ne hfy
    exact ⟨C.smul_mem (mem_Ioi.mp hri).le hyC, by simp [ne_of_gt hri, hy0]⟩

/-- If there is a linear map that is positive on the entire cone except 0, the cone is the closed
sMul-span of any positive level set of the map. -/
lemma eq_Ici_zero_smul_inter_preimage_of_pos_of_ne_bot {C : PointedCone R M} {f : M →ₗ[R] R} {r : R}
    (hf : ∀ x ∈ C, x ≠ 0 → 0 < f x) (hr : 0 < r) (hC : C ≠ ⊥) :
    C = Set.Ici (0 : R) • ((C : Set M) ∩ f ⁻¹' {r}) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp only [SetLike.mem_coe, zero_mem, true_iff]
    use 0, le_rfl
    simp only [mem_inter_iff, SetLike.mem_coe, mem_preimage, mem_singleton_iff, zero_smul, and_true]
    obtain ⟨x, hx⟩ := C.ne_bot_iff.mp hC
    use r • (f x)⁻¹ • x
    have fxpos : 0 < f x := hf x hx.1 hx.2
    simp only [← smul_assoc, smul_eq_mul, map_smul]
    refine ⟨C.smul_mem (mul_pos hr (inv_pos.mpr fxpos)).le hx.1, ?_⟩
    simp [mul_assoc, inv_mul_cancel₀ fxpos.ne.symm]
  · constructor <;> intro h
    · apply Set.smul_subset_smul_right Ioi_subset_Ici_self
      exact eq_Ioi_zero_smul_inter_preimage_of_pos hf hr ▸ mem_sdiff_singleton.mpr ⟨h, hx⟩
    · obtain ⟨_, hr, _, hy, b⟩ := h
      simpa [← b] using C.smul_mem hr (mem_of_mem_inter_left hy)

end Field

end PointedCone
