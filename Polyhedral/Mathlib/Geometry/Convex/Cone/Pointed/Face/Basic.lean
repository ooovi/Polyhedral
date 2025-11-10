/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Quotient.Basic
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual


/-!
# Faces of pointed cones
-/

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
in
structure IsFaceOf (F C : PointedCone R M) where
  subset : F ≤ C
  left_mem_of_smul_add_mem :
    ∀ {x y : M} {a b : R}, x ∈ C → y ∈ C → 0 < a → 0 < b → a • x + b • y ∈ F → x ∈ F

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] {C C₁ C₂ F F₁ F₂ : PointedCone R M}

@[refl]
lemma refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun ⦃_⦄ a ↦ a, fun hx _ _ _ _ ↦ hx⟩
lemma rfl {C : PointedCone R M} : C.IsFaceOf C := ⟨fun ⦃_⦄ a ↦ a, fun hx _ _ _ _ ↦ hx⟩

lemma inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.subset, Set.inter_subset_right.trans h₂.subset⟩
  simp only [Submodule.mem_inf, and_imp]
  intros x y a b xc₁ xc₂ yc₁ yc₂ a0 b0 hz₁ hz₂
  constructor
  · exact h₁.left_mem_of_smul_add_mem xc₁ yc₁ a0 b0 hz₁
  · exact h₂.left_mem_of_smul_add_mem xc₂ yc₂ a0 b0 hz₂

theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C := by
  refine Eq.mp ?_ (inf h₁ h₂)
  simp

theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) := by
  refine Eq.mp ?_ (inf h₁ h₂)
  simp

lemma trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  refine ⟨h₁.subset.trans h₂.subset, fun hx hy a0 b0 h ↦ ?_⟩
  refine h₁.2 (h₂.2 hx hy a0 b0 (h₁.subset h)) ?_ a0 b0 h
  refine h₂.left_mem_of_smul_add_mem hy hx b0 a0 ?_
  rw [add_comm] at h
  exact h₁.subset h

lemma inf_isFaceOf_inf (h : F₁.IsFaceOf C₁) (C₂ : PointedCone R M) : (F₁ ⊓ C₂).IsFaceOf (C₁ ⊓ C₂) :=
  inf h rfl

lemma isExtreme (h : F.IsFaceOf C) : IsExtreme R (E := M) C F := by
  refine ⟨h.subset, ?_⟩
  rintro x xc y yc z zf ⟨a, b, a0, b0, -, hz⟩
  apply h.left_mem_of_smul_add_mem xc yc a0 b0
  rwa [← hz] at zf

end Semiring

/-!
### Joins
-/

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C D F G : PointedCone R M}

lemma sup (hFC : F.IsFaceOf C) (hGD : G.IsFaceOf D)
    (hCD : ∀ {x}, x ∈ Submodule.span R C ∧ x ∈ Submodule.span (M := M) R D → x = 0) :
    (F ⊔ G).IsFaceOf (C ⊔ D) := by
  constructor
  · simp only [sup_le_iff]
    constructor
    · apply le_trans _ le_sup_left
      convert hFC.subset
    · apply le_trans _ le_sup_right
      convert hGD.subset
  · intros _ _ a b xs ys a0 b0 h
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
      (mem hx' hx'') (hFC.subset hxf) (mem hy' hy'') (hGD.subset hyg) hCD this
    refine ⟨x', ?_, y', ?_, hfx⟩
    · exact hFC.left_mem_of_smul_add_mem hx' hx'' a0 b0 (by rwa [this.1])
    · exact hGD.left_mem_of_smul_add_mem hy' hy'' a0 b0 (by rwa [this.2])

end Ring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s : Set M}

/-!
### Equivalent definitions of isFaceOf on fields
-/

lemma iff_mem_of_mul_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ {x y : M} {c : R}, x ∈ C → y ∈ C → 0 < c → c • x + y ∈ F → x ∈ F := by
  constructor
  · intro f; refine ⟨f.subset, ?_⟩
    intros x y c xC yC cpos h
    apply f.left_mem_of_smul_add_mem xC yC cpos zero_lt_one
    simp [h]
  · intro h
    constructor
    · exact h.1
    · intros x y a b xC yC a0 b0 hab
      exact h.2 xC (Submodule.smul_mem C ⟨_, le_of_lt b0⟩ yC) a0 hab

lemma iff_mem_of_add_mem :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ F → x ∈ F := by
  constructor <;> intro h
  · have := iff_mem_of_mul_add_mem.mp h
    refine ⟨this.1, fun xC yC => ?_⟩
    convert this.2 xC yC (zero_lt_one)
    simp
  · apply iff_mem_of_mul_add_mem.mpr ⟨h.1, fun xC yC c0 hcxy => ?_⟩
    have cxF := h.2 (smul_mem _ (le_of_lt c0) xC) yC hcxy
    convert smul_mem _ (inv_nonneg.mpr (le_of_lt c0)) cxF
    simp [← smul_assoc, smul_eq_mul, mul_comm, Field.mul_inv_cancel _ (ne_of_lt c0).symm]

lemma span_nonneg_lc_mem {f : F.IsFaceOf (span R s)} {n : ℕ} {c : Fin n → { c : R // 0 ≤ c }}
    {g : Fin n → s} (h : ∑ i, c i • (g i).val ∈ F) {i : Fin n} (cpos : 0 < c i) :
    (g i).val ∈ F := by
  induction n with
  | zero => exact isEmptyElim i
  | succ n ih =>
      have : ∑ i ∈ {i}ᶜ, c i • (g i).val ∈ span R s :=
        Submodule.sum_smul_mem _ _ (fun _ _ => subset_span (Subtype.coe_prop _))
      rw [Fintype.sum_eq_add_sum_compl i] at h
      exact (iff_mem_of_mul_add_mem.mp f).2 (subset_span (Subtype.coe_prop _)) this cpos h

lemma iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ ≤ F₂ := by
  constructor
  · exact IsFaceOf.subset
  · rw [iff_mem_of_mul_add_mem] at ⊢ h₁
    exact fun h => ⟨h, fun hx hy => h₁.2 (h₂.subset hx) (h₂.subset hy)⟩

lemma iff_of_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂ ≤ F₁) :
    F₂.IsFaceOf C ↔ F₂.IsFaceOf F₁ :=
  ⟨fun h => (iff_le h h₁).mpr h₂, fun h => trans h h₁⟩

end Field

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {C F : PointedCone R M}

/-- The lineal space of a cone `C` is a face of `C`. -/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  suffices ∀ {x y : M}, x ∈ C → y ∈ C → x + y ∈ ↑C.lineal → x ∈ ↑C.lineal by
    exact iff_mem_of_add_mem.mpr ⟨PointedCone.lineal_le C, this⟩
  intros _ _ xc yc xyf
  simp only [lineal_mem, neg_add_rev, xc, true_and] at xyf ⊢
  have := add_mem xyf.2 yc
  simp only [neg_add_cancel_comm] at this
  assumption

-- lemma lineal_le {C : PointedCone R M} (h : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ F → x ∈ F) :
--   C.lineal ≤ F := by
--   intro x xl
--   apply lineal_mem.mp at xl
--   exact h x xl.1 (-x) xl.2 (by simp only [add_neg_cancel, zero_mem])

/-- Mapping a face using an injective linear map yields a face of the image of `C`. -/
lemma map_iff {f : M →ₗ[R] N} (hf : Function.Injective f) :
    (PointedCone.map f F).IsFaceOf (.map f C) ↔ F.IsFaceOf C := by
  simp [iff_mem_of_add_mem, mem_map]
  constructor <;> intro ⟨sub, hF⟩
  · refine ⟨fun x xf => ?_, fun hx hy hxy => ?_⟩
    · obtain ⟨y, yC, hy⟩ := Submodule.mem_map.mp <| sub (Submodule.mem_map_of_mem xf)
      rw [hf hy] at yC
      assumption
    · obtain ⟨x', hx', hx'f⟩ :=
        hF _ hx (Eq.refl _) _ hy (Eq.refl _) _ hxy (f.map_add _ _)
      rwa [hf hx'f] at hx'
  · refine ⟨Submodule.map_mono sub, fun x xc xf _ yc yf _ _ h => ⟨x, hF xc yc ?_, xf⟩⟩
    rw [← xf, ← yf, ← f.map_add] at h
    rwa [← hf h]

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
    · intro x y xC yC h
      rw [← ec x] at h xC ⊢
      rw [← ec y] at h yC
      exact hF xC yC h
  · exact ⟨Submodule.comap_mono sub, hF⟩

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
def inter (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, IsFaceOf.inf_left F₁.isFaceOf F₂.isFaceOf⟩

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
  · intros x xp
    rw [Submodule.mem_prod] at xp ⊢
    exact ⟨F₁.isFaceOf.subset xp.1, F₂.isFaceOf.subset xp.2⟩
  · simp only [Submodule.mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
    intros _ _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 b0 hab₁ hab₂
    constructor
    · exact F₁.isFaceOf.left_mem_of_smul_add_mem xc₁ yc₁ a0 b0 hab₁
    · exact F₂.isFaceOf.left_mem_of_smul_add_mem xc₂ yc₂ a0 b0 hab₂

end Prod

end Semiring

section Field

section Prod

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ F : PointedCone R M} {C₂ : PointedCone R N}

open Submodule

/-- The face of `C₁` obtained by projecting to the left component of a face `F ≤ C₁ × C₂`. -/
def prod_left (F : Face (C₁.prod C₂)) : Face C₁ := {
  map (LinearMap.fst _ M N) F with
  isFaceOf := by
    constructor
    · intro x xm
      simp [LinearMap.fst_apply] at xm
      convert (Set.mem_prod.mp <| F.isFaceOf.subset xm.choose_spec).1
    · simp only [toPointedCone, mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
      intros x y _ b xc yc a0 b0 z h
      use 0
      refine F.isFaceOf.left_mem_of_smul_add_mem (x := (x, 0)) (y := (y, b⁻¹ • z)) ?_ ?_ a0 b0 ?_
      · exact mem_prod.mp ⟨xc, zero_mem C₂⟩
      · exact mem_prod.mp ⟨yc, smul_mem C₂ (le_of_lt (inv_pos_of_pos b0)) (F.isFaceOf.subset h).2⟩
      · simpa [← smul_assoc, mul_inv_cancel₀ (ne_of_lt b0).symm]
}

/-- The face of `C₂` obtained by projecting to the right component of a face `F ≤ C₁ × C₂`. -/
def prod_right (F : Face (C₁.prod C₂)) : Face C₂ := {
  map (LinearMap.snd _ M N) F with
  isFaceOf := by
    constructor
    · intro x xm
      simp [LinearMap.snd_apply] at xm
      convert (Set.mem_prod.mp <| F.isFaceOf.subset xm.choose_spec).2
    · simp only [toPointedCone, mem_map, LinearMap.snd_apply, Prod.exists, exists_eq_right,
      forall_exists_index]
      intros x y _ b xc yc a0 b0 z h
      use 0
      refine F.isFaceOf.left_mem_of_smul_add_mem (x := (0, x)) (y := (b⁻¹ • z, y)) ?_ ?_ a0 b0 ?_
      · exact mem_prod.mp ⟨zero_mem C₁, xc⟩
      · exact mem_prod.mp ⟨smul_mem C₁ (le_of_lt (inv_pos_of_pos b0)) (F.isFaceOf.subset h).1, yc⟩
      · simpa [← smul_assoc, mul_inv_cancel₀ (ne_of_lt b0).symm]
  }

@[simp]
lemma prod_prod_left (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_left = F₁ := by
  simp [prod_left, prod]
  sorry

@[simp]
lemma prod_prod_right (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).prod_right = F₂ := by
  simp [prod_right, prod]
  sorry

lemma prod_left_prod_right (G : Face (C₁.prod C₂)) : G.prod_left.prod G.prod_right = G := by
  simp only [prod_right, prod_left, prod]
  ext x
  constructor
  · simp
    intro y yn z zm
    sorry
  · simp; intro h; exact ⟨⟨x.2, h⟩, ⟨x.1, h⟩⟩

end Prod

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ C₂ F : PointedCone R M} {s t : Set M}

/-!
#### Restrict
-/
abbrev span (F : Face C) : Submodule R M := Submodule.span R F

/-- The face of `F₁` obtained by intersecting `F₁` with another of `C`'s faces. -/
def restrict (F₁ F₂ : Face C) : Face (F₁ : PointedCone R M) :=
  ⟨F₁ ⊓ F₂, (F₁.isFaceOf.iff_of_le inf_le_left).mp (F₁.isFaceOf.inf_left F₂.isFaceOf)⟩

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
  intros x y xd
  simp only [mem_dual, SetLike.mem_coe, Submodule.mem_inf, map_add, Submodule.restrictScalars_mem,
    Submodule.mem_dual, xd, true_and, and_imp]
  intros yC _ n'on _ mF
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
