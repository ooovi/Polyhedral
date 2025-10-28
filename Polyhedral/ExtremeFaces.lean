/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-- -/
import Mathlib.Analysis.Convex.Extreme
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Dual


/-!
# Faces of pointed cones

-/

namespace PointedCone

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

abbrev IsFaceOf (F C : PointedCone R M) := IsExtreme R (E := M) C F

variable {C F F₁ F₂ : PointedCone R M}

-- TODO does this make sense to have?
abbrev isFaceOf_self (C : PointedCone R M) : C.IsFaceOf C := IsExtreme.rfl

abbrev isFaceOf.trans (h₁ : F₁.IsFaceOf F) (h₂ : F.IsFaceOf F₂) : F₁.IsFaceOf F₂ :=
  IsExtreme.trans h₂ h₁

abbrev IsFaceOf.inter (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  IsExtreme.inter h₁ h₂

lemma IsFaceOf.le_self {F : PointedCone R M} (hF : F.IsFaceOf C) : F ≤ C := by sorry


/-- A face of a pointed cone `C` is a pointed cone that is an extreme subset of `C`. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

def face_self (C : PointedCone R M) : Face C := ⟨_, isFaceOf_self C⟩

alias face_top := face_self

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) := ⟨C.face_self⟩
instance {S : Submodule R M} : CoeDep (Submodule R M) S (Face (S : PointedCone R M)) :=
    ⟨(S : PointedCone R M).face_self⟩

-- does not work without the second CoeDep
example {C : Submodule R M} : Face (C : PointedCone R M) := C


namespace Face

def of_IsFaceOf (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

-- we can't have an actual Coe instance because coercion target throws away the information `C`
@[coe, simp]
def toPointedCone {C : PointedCone R M} (f : Face C) := f.toSubmodule

instance : CoeOut (Face (M := M) (R := R) C) (PointedCone R M) where
coe f := f.toSubmodule

instance : SetLike (Face C) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

@[simp, norm_cast]
theorem toPointedCone_eq_iff {F₁ F₂ : Face C} :
    F₁.toPointedCone = F₂.toPointedCone ↔ F₁ = F₂ := by
  constructor <;> intro h <;> try rw [mk.injEq] at *; exact h


/-!
## Partial Order and Lattice on Faces
-/

instance partialOrder : PartialOrder (Face C) where
  le F₁ F₂ := IsFaceOf F₁.toPointedCone F₂.toPointedCone -- should be F₁ ≤ F₂
  lt F₁ F₂ := IsFaceOf F₁.toPointedCone F₂.toPointedCone ∧
    ¬(IsFaceOf F₂.toPointedCone F₁.toPointedCone)
  le_refl F := IsExtreme.rfl
  le_trans F₁ F₂ F h₁ h₂ := IsExtreme.trans h₂ h₁
  lt_iff_le_not_ge F C := by simp
  le_antisymm F₁ F₂ h₁ h₂ := by convert IsExtreme.antisymm h₂ h₁; norm_cast

example (F G : Face C) (h : F ≤ G) : (F : Set M) ≤ G := sorry -- `h` does not work right now

@[simp]
theorem toPointedCone_le {F₁ F₂ : Face C} (h : F₁ ≤ F₂) :
    F₁.toPointedCone ≤ F₂.toPointedCone := by
  intro x xF₁; simp [LE.le] at h; exact h.subset xF₁

/- Note: `face_le_self` is comparison as pointed cones, `le_self` is comparison as faces.
  We should not need two lemmas. We need to change `partialPrder`. -/

abbrev face_le_self (F : Face C) : F ≤ C := F.isFaceOf.subset

abbrev le_self (F : Face C) : F ≤ (C : Face C) := sorry -- F.isFaceOf.subset

end Face

instance : OrderTop (Face C) where
  top := C
  le_top F := F.le_self

instance face_nonempty {C : PointedCone R M} : Nonempty (Face C) := ⟨⊤⟩

instance face_inhabited {C : PointedCone R M} : Inhabited (Face C) := ⟨⊤⟩

namespace Face

/-!
### Supremum

-/

/-- The supremum of two faces `F₁, F₂` of `C` is the smallest face of `C` that has both `F₁` and
`F₂` as faces. -/
def sup (F₁ F₂ : Face C) : Face C := by
  refine ⟨sInf { F : PointedCone R M | F.IsFaceOf C ∧ ↑F₁ ≤ F ∧ ↑F₂ ≤ F}, ?_⟩
  constructor
  · intros _ sm
    simp at sm ⊢
    exact sm C C.isFaceOf_self F₁.face_le_self F₂.face_le_self
  · simp; intros _ xc _ yc _ zfs zo F FFs FF₁ FF₂
    exact FFs.left_mem_of_mem_openSegment xc yc (zfs F FFs FF₁ FF₂) zo

private lemma left_mem_of_mem_openSegment {F₁ F₂ : Face C} :
    ∀ x ∈ F₂, ∀ y ∈ F₂, ∀ z ∈ F₁, z ∈ openSegment R x y → x ∈ F₁ := by
  intros _ asup _ bsup _ zF zo
  exact F₁.isFaceOf.left_mem_of_mem_openSegment (face_le_self _ asup) (face_le_self _ bsup) zF zo

/-- The infimum of two faces `F₁, F₂` of `C` is the infimum of the submodules `F₁` and `F₂`. -/
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, IsFaceOf.inter F₁.isFaceOf F₂.isFaceOf⟩

instance : Lattice (Face C) :=
  { partialOrder with
    inf := inf
    inf_le_left F₁ F₂ := by
      refine ⟨fun _ ai => ai.1, fun _ _ _ _ _ zfs zo => ?_⟩
      refine (F₁.isFaceOf.inter F₂.isFaceOf).left_mem_of_mem_openSegment ?_ ?_ zfs zo <;>
      apply F₁.isFaceOf.subset <;> assumption
    inf_le_right F₁ F₂ := by
      refine ⟨fun _ ai => ai.2, fun _ _ _ _ _ zfs zo => ?_⟩
      refine (F₁.isFaceOf.inter F₂.isFaceOf).left_mem_of_mem_openSegment ?_ ?_ zfs zo <;>
      apply F₂.isFaceOf.subset <;> assumption
    le_inf  F₁ F₂ F₃ h₁₂ h₂₃:= by
      simp only [LE.le] at h₁₂ h₂₃
      refine ⟨fun _ af => ⟨h₁₂.subset af, h₂₃.subset af⟩, fun _ _ _ _ _ zfs zo => ?_⟩
      refine h₁₂.left_mem_of_mem_openSegment ?_ ?_ zfs zo <;>
      apply Set.mem_of_mem_inter_left <;> assumption
    sup := sup
    le_sup_left F₁ F₂ := by
      constructor
      · simp only [SetLike.coe_subset_coe]; exact le_sInf (fun F' F's => F's.2.1)
      · exact left_mem_of_mem_openSegment
    le_sup_right F₁ F₂ := by
      constructor
      · simp only [SetLike.coe_subset_coe]; exact le_sInf (fun F' F's => F's.2.2)
      · exact left_mem_of_mem_openSegment
    sup_le F₁ F₂ F₃ f₁₂ f₂₃:= by
      constructor
      · intros x xs
        have : F₃.toPointedCone ∈ { F : PointedCone R M | F.IsFaceOf C ∧ ↑F₁ ≤ F ∧ ↑F₂ ≤ F} :=
          ⟨F₃.isFaceOf, toPointedCone_le f₁₂, toPointedCone_le f₂₃⟩
        exact sInf_le this xs
      · exact left_mem_of_mem_openSegment }

end Face

lemma sub_eq_sub_of_add_eq_add {a b c d : M} (h : a + b = c + d) : a - c = d - b := by
  calc a - c = a + b - c - b := by abel
           _ = c + d - c - b := by rw [h]
           _ = d - b         := by abel

end Semiring

/-!
### Joins

-/
section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

open Submodule in
lemma uniq_decomp_of_zero_inter {C D : PointedCone R M} {xC xD yC yD : M}
    (mxc : xC ∈ C) (myc : yC ∈ C) (mxd : xD ∈ D) (myd : yD ∈ D)
    (hCD : ∀ {x}, x ∈ Submodule.span R C ∧ x ∈ Submodule.span (M := M) R D → x = 0)
    (s : xC + xD = yC + yD) :
    xC = yC ∧ xD = yD := by
  let sub_mem_span {C x y} (mx : x ∈ C) (my : y ∈ C) :=
    (Submodule.span (M := M) R C).sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
  constructor
  · refine (sub_eq_zero.mp <| hCD ⟨sub_mem_span mxc myc, ?_⟩).symm
    simp [sub_eq_sub_of_add_eq_add s.symm]
    exact sub_mem_span myd mxd
  · refine (sub_eq_zero.mp <| hCD ⟨?_, sub_mem_span mxd myd⟩).symm
    simp [← sub_eq_sub_of_add_eq_add s]
    exact sub_mem_span myc mxc

lemma sup_isFaceOf_sup {C D F G : PointedCone R M} (hFC : F.IsFaceOf C) (hGD : G.IsFaceOf D)
    (hCD : ∀ {x}, x ∈ Submodule.span R C ∧ x ∈ Submodule.span (M := M) R D → x = 0) :
    (F ⊔ G).IsFaceOf (C ⊔ D) := by
  constructor
  · simp only [SetLike.coe_subset_coe, sup_le_iff]
    constructor
    · apply le_trans _ le_sup_left
      convert hFC.subset
    · apply le_trans _ le_sup_right
      convert hGD.subset
  · simp; intros x xm y ym z zu zo

    wlog h : ¬(x ∈ Submodule.span R (SetLike.coe C) ∧ x ∈ Submodule.span R (SetLike.coe D))
    · push_neg at h
      have := hCD h
      subst this
      exact zero_mem _
    · push_neg at h
      obtain ⟨xC, xCM, xD, xDM, xx⟩ := Submodule.mem_sup.mp xm
      obtain ⟨yC, yCM, yD, yDM, yy⟩ := Submodule.mem_sup.mp ym
      obtain ⟨zF, zFM, zG, zGM, zz⟩ := Submodule.mem_sup.mp zu

      have : zF ∈ openSegment R xC yC ∧ zG ∈ openSegment R xD yD := by
        rw [openSegment, Set.mem_setOf, ← xx, ← yy, ← zz] at zo
        obtain ⟨a, b, a0, b0, ab1, abz⟩ := zo
        have : (a • xC + b • yC) + (a • xD + b • yD) = zF + zG := by
          rw [← abz, smul_add, smul_add]
          abel

        let mem {C : PointedCone R  M} {x y} (xCM yCM) : a • x + b • y ∈ C :=
          C.add_mem (C.smul_mem (le_of_lt a0) xCM) (C.smul_mem (le_of_lt b0) yCM)

        have := uniq_decomp_of_zero_inter
          (mem xCM yCM) (hFC.subset zFM) (mem xDM yDM) (hGD.subset zGM) hCD this
        constructor
        use a, b, a0, b0, ab1, this.1
        use a, b, a0, b0, ab1, this.2

      apply Submodule.mem_sup.mpr
      use xC, hFC.left_mem_of_mem_openSegment xCM yCM zFM this.1
      use xD, hGD.left_mem_of_mem_openSegment xDM yDM zGM this.2

end Ring

/-!
### Intersections

-/
section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F F₁ F₂ : PointedCone R M} {s t : Set M}

lemma scale_sum_mem {F : Face C} {x y : M} {c : R} (cpos : 0 < c) (hx : x ∈ C) (hy : y ∈ C)
   (hc : c • y + x ∈ F) : x ∈ F ∧ y ∈ F := by
  let r := 1 / (1 + c)
  have rpos := div_pos zero_lt_one (add_pos zero_lt_one cpos)
  have : r • (c • y + x) ∈ openSegment R x y := by
      simp [openSegment]
      use r, rpos, c • r, smul_pos cpos rpos
      constructor
      · simp only [smul_eq_mul, mul_div, mul_one, ← add_div, r]; exact div_self (by positivity)
      · simp [← smul_assoc, mul_comm, add_comm]
  have sf := F.toPointedCone.smul_mem ⟨r, le_of_lt rpos⟩ hc
  constructor
  · exact F.isFaceOf.left_mem_of_mem_openSegment hx hy sf this
  · exact F.isFaceOf.right_mem_of_mem_openSegment hx hy sf this

lemma scale_sum_mem_iff : F.IsFaceOf C ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ c : R, 0 < c → c • x + y ∈ F → x ∈ F
  := by sorry

lemma span_nonneg_lc_mem {F : (span R s).Face} {n : ℕ} {c : Fin n → { c : R // 0 ≤ c }}
    {g : Fin n → s} (h : ∑ i, c i • (g i).val ∈ F.toSubmodule) {i : Fin n} (cpos : 0 < c i) :
    (g i).val ∈ F := by
  induction n with
  | zero => exact isEmptyElim i
  | succ n ih =>
      have : ∑ i ∈ {i}ᶜ, c i • (g i).val ∈ span R s :=
        Submodule.sum_smul_mem _ _ (fun _ _ => subset_span (Subtype.coe_prop _))
      rw [Fintype.sum_eq_add_sum_compl i] at h
      obtain ⟨l, r⟩ := scale_sum_mem cpos this (subset_span (Subtype.coe_prop _)) h
      exact r

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
      exact Set.mem_inter (Subtype.coe_prop (g i)) (span_nonneg_lc_mem h.2 (pos_of_ne_zero hh))

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
  have := congrArg (fun s : s.powerset => span (E := M) R s) FF
  simp [(exists_fg_span_subset_face _).choose_spec.2] at this
  exact Face.toPointedCone_eq_iff.mp this


/-!
## Particular Faces

-/

lemma isFaceOf_lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  constructor
  · exact PointedCone.lineal_le C
  · simp
    intros x xC y yC z zlin zop
    rw [lineal_mem] at zlin ⊢
    refine ⟨xC, ?_⟩

    simp [openSegment] at zop
    obtain ⟨a, a0, _, b0, _, zab⟩ := zop

    rw [← one_smul R (-x), ← Field.mul_inv_cancel a (ne_of_lt a0).symm, mul_comm, mul_smul]
    apply C.smul_mem (r := a⁻¹) (inv_nonneg_of_nonneg (G₀ := R) <| le_of_lt a0)

    have := congrArg Neg.neg zab
    rw [neg_add, ← smul_neg a] at this
    apply eq_sub_of_add_eq at this
    rw [sub_neg_eq_add] at this
    rw [this]

    exact C.add_mem zlin.2 (C.smul_mem (le_of_lt b0) yC)

def face_lineal (C : PointedCone R M) : Face C := ⟨_, isFaceOf_lineal C⟩

alias face_bot := face_lineal

lemma IsFaceOf.lineal_le {F : PointedCone R M} (hF : F.IsFaceOf C) : C.lineal ≤ F := by sorry

lemma Face.lineal_le {C : PointedCone R M} (F : Face C) : C.face_lineal ≤ F := by sorry

instance : OrderBot (Face C) where
  bot := C.face_lineal
  bot_le F := F.lineal_le


-- TODO: move the below to the other lineal lemmas.

lemma span_inter_lineal_eq_lineal' (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  convert span_inter_face_span_inf_face ⟨_, isFaceOf_lineal _⟩
  simp
  exact (isFaceOf_lineal _).subset

lemma FG.lineal_fg' {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by
  convert FG.face_fg_of_fg hC ⟨_, isFaceOf_lineal _⟩
  simp

end Field

/-!
### Faces of the dual cone

-/

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R)
in
def subdual (C F : PointedCone R M) : PointedCone R N :=
  (dual p C) ⊓ (.dual p F : Submodule R N)

section Field

variable {R : Type*} [Field R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R) {C F : PointedCone R M}

/-- The subdual of a face is a face of the dual. -/
lemma IsFaceOf.subdual_dual (hF : F.IsFaceOf C) :
    (subdual p C F).IsFaceOf (dual p C) := by
  unfold subdual
  refine ⟨by simp, ?_⟩
  intros _ xd
  simp [xd]
  intros _ nC _ n'C mn' n'on _ mF
  apply eq_of_le_of_ge
  · exact xd (hF.subset mF)
  · simp [openSegment] at n'on
    obtain ⟨_, apos, _, _, -, zxy⟩ := n'on
    simp_rw [← zxy, LinearMap.map_add, LinearMap.map_smul] at mn'
    simp [← (inv_mul_eq_iff_eq_mul₀ (ne_of_lt apos).symm).mpr <| tsub_eq_of_eq_add (mn' mF)]
    have := nC (hF.subset mF)
    positivity

/-- The subdual is antitone. -/
lemma subdual_antitone : Antitone (subdual p C) := by
  intros _ _ hF
  unfold subdual
  gcongr
  exact Submodule.dual_le_dual hF

section IsDualClosed

variable (hC : C.IsDualClosed p)

/-- The subdual is injective. -/
-- only for fg
lemma subdual_inj (hC : C.IsDualClosed p) : Function.Injective (subdual p C) := sorry

/-- The subdual is involutive. -/
-- only for fg
lemma subdual_subdual {F : PointedCone R M} :
    subdual p.flip (dual p C) (subdual p C F) = F := sorry

/-- The subdual is strictly antitone. -/
lemma subdual_antitone_iff {F₁ F₂ : PointedCone R M} :
    subdual p C F₁ ≤ subdual p C F₂ ↔ F₂ ≤ F₁ where
  mpr := fun h => subdual_antitone p h
  mp := sorry

end IsDualClosed

end Field

end PointedCone
