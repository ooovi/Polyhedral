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

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
in
abbrev IsFaceOf (F C : PointedCone R M) := IsExtreme R (E := M) C F

namespace IsFaceOf

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

-- TODO does this make sense to have?
lemma self (C : PointedCone R M) : C.IsFaceOf C := IsExtreme.rfl

lemma trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C :=
  IsExtreme.trans h₂ h₁

lemma inf (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  IsExtreme.inter h₁ h₂

lemma le_self {F : PointedCone R M} (hF : F.IsFaceOf C) : F ≤ C := hF.subset

end Semiring

/-!
### Joins

-/

section Ring

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

#check sub_eq_sub_iff_add_eq_add

lemma sub_eq_sub_of_add_eq_add {a b c d : M} (h : a + b = c + d) : a - c = d - b := by
  calc a - c = a + b - c - b := by abel
           _ = c + d - c - b := by rw [h]
           _ = d - b         := by abel

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

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F : PointedCone R M} {s : Set M}

lemma isFaceOf_iff :
    F.IsFaceOf C ↔ F ≤ C ∧ ∀ x ∈ C, ∀ y ∈ C, ∀ c : R, 0 < c → c • x + y ∈ F → x ∈ F := by
  constructor
  · intro f; refine ⟨f.subset, ?_⟩
    intros x xC y yC c cpos h
    let r := 1 / (1 + c)
    have rpos := div_pos zero_lt_one (add_pos zero_lt_one cpos)
    have : r • (c • x + y) ∈ openSegment R x y := by
      simp [openSegment]
      use c • r, smul_pos cpos rpos, r, rpos
      constructor
      · simp only [smul_eq_mul, mul_div, mul_one, ← add_div, r, add_comm]
        exact div_self (by positivity)
      · simp [← smul_assoc, mul_comm, add_comm]
    have sf := F.smul_mem (le_of_lt rpos) h
    exact f.left_mem_of_mem_openSegment xC yC sf this
  · intro h
    constructor
    · exact h.1
    · intros x xC y yC z zF zo
      obtain ⟨a, b, apos, bpos, _, rfl⟩ := zo
      exact h.2 x xC (b • y) (C.smul_mem (le_of_lt bpos) yC) a apos zF

lemma span_nonneg_lc_mem {f : F.IsFaceOf (span R s)} {n : ℕ} {c : Fin n → { c : R // 0 ≤ c }}
    {g : Fin n → s} (h : ∑ i, c i • (g i).val ∈ F) {i : Fin n} (cpos : 0 < c i) :
    (g i).val ∈ F := by
  induction n with
  | zero => exact isEmptyElim i
  | succ n ih =>
      have : ∑ i ∈ {i}ᶜ, c i • (g i).val ∈ span R s :=
        Submodule.sum_smul_mem _ _ (fun _ _ => subset_span (Subtype.coe_prop _))
      rw [Fintype.sum_eq_add_sum_compl i] at h
      exact (isFaceOf_iff.mp f).2 _ (subset_span (Subtype.coe_prop _)) _ this _ cpos h

end Field

/-!
### Faces of the dual cone

-/

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R)
in
def subdual (C F : PointedCone R M) : PointedCone R N :=
  (dual p C) ⊓ (.dual p F : Submodule R N)

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (p : M →ₗ[R] N →ₗ[R] R) {C F : PointedCone R M}

/-- The subdual of a face is a face of the dual. -/
lemma subdual_dual (hF : F.IsFaceOf C) :
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


lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
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

end Field

end IsFaceOf

/-!
## Bundled Face

-/

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

/-- A face of a pointed cone `C` is a pointed cone that is an extreme subset of `C`. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

def face_self (C : PointedCone R M) : Face C := ⟨_, IsFaceOf.self C⟩

alias face_top := face_self

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) := ⟨C.face_self⟩
instance {S : Submodule R M} : CoeDep (Submodule R M) S (Face (S : PointedCone R M)) :=
    ⟨(S : PointedCone R M).face_self⟩

-- does not work without the second CoeDep
example {C : Submodule R M} : Face (C : PointedCone R M) := C

namespace Face

-- def of_IsFaceOf (hF : F.IsFaceOf C) : Face C := ⟨F, hF⟩

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

instance partialOrder : PartialOrder (Face C) := inferInstance

example (F G : Face C) (h : F ≤ G) : (F : Set M) ≤ G := h

@[simp]
theorem toPointedCone_le_iff {F₁ F₂ : Face C} : F₁ ≤ F₂ ↔ F₁.toPointedCone ≤ F₂.toPointedCone := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.subset

instance face_nonempty {C : PointedCone R M} : Nonempty (Face C) := ⟨⊤⟩

instance face_inhabited {C : PointedCone R M} : Inhabited (Face C) := ⟨⊤⟩

/-!
### Infimum, supremum and lattice

-/

/-- The infimum of two faces `F₁, F₂` of `C` is the infimum of the submodules `F₁` and `F₂`. -/
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf F₂.isFaceOf⟩

instance : InfSet (Face C) := ⟨fun S =>
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp; intros _ xc _ yc _ _ zfs zo
        simp [xc]; intros F Fs
        exact F.isFaceOf.left_mem_of_mem_openSegment xc yc (zfs F Fs) zo
}⟩

instance : SemilatticeInf (Face C) where
  inf := inf
  inf_le_left _ _ _ xi := xi.1
  inf_le_right _ _ _ xi := xi.2
  le_inf _ _ _ h₁₂ h₂₃ _ xi := ⟨h₁₂ xi, h₂₃ xi⟩

instance : CompleteSemilatticeInf (Face C) where
  __ := instSemilatticeInf
  sInf_le S f fS := by
    simp only [toPointedCone_le_iff, toPointedCone]
    refine inf_le_of_right_le ?_
    simp [LE.le]
    intro x xs
    exact xs f fS
  le_sInf S f fS := by
    simp [sInf]
    refine ⟨f.isFaceOf.subset, ?_⟩
    simp [LE.le]
    intro x xf s sm
    exact fS s sm xf

/-- The supremum of two faces `F₁, F₂` of `C` is the smallest face of `C` that has both `F₁` and
`F₂` as faces. -/
def sup (F₁ F₂ : Face C) : Face C := sInf {F : Face C | F₁ ≤ F ∧ F₂ ≤ F}

instance : SemilatticeSup (Face C) where
  sup := sup
  le_sup_left _ _ := le_sInf (fun _ Fs => Fs.1)
  le_sup_right _ _ := le_sInf (fun _ Fs => Fs.2)
  sup_le _ _ _ h₁₂ h₂₃ := sInf_le (Set.mem_sep h₁₂ h₂₃)


/-- `sSup S` of a set `S` of faces of `C` is the smallest face of `C` that has all members of `S` as
faces. -/
def sSup (S : Set (Face C)) : Face C := sInf { F : Face C | ∀ F' ∈ S, F' ≤ F}

instance : SupSet (Face C) :=
  ⟨fun S => {
    carrier := sSup S
    add_mem' aS bS := Submodule.add_mem _ aS bS
    zero_mem' := Submodule.zero_mem _
    smul_mem' _ _ h := Submodule.smul_mem _ _ h
    isFaceOf := (sSup S).isFaceOf
  }⟩

instance : CompleteSemilatticeSup (Face C) where
  __ := instSemilatticeSup
  sSup := sSup
  sSup_le _ _ fS := sInf_le_of_le fS le_rfl
  le_sSup _ f fS := le_sInf_iff.mpr <| fun _ a ↦ a f fS

instance : Lattice (Face C) where

end Face

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  {C F : PointedCone R M} {s t : Set M}

/-!
### Intersections

-/

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
  have := congrArg (fun s : s.powerset => span (E := M) R s) FF
  simp [(exists_fg_span_subset_face _).choose_spec.2] at this
  exact Face.toPointedCone_eq_iff.mp this

/-!
## Particular Faces

-/

def face_lineal : Face C := ⟨C.lineal, IsFaceOf.lineal C⟩

lemma Face.lineal_le {C : PointedCone R M} (F : Face C) : C.face_lineal ≤ F := sorry


instance : OrderBot (Face C) where
  bot := C.face_lineal
  bot_le F := F.lineal_le

instance : BoundedOrder (Face C) where

instance : CompleteLattice (Face C) where


-- TODO: move the below to the other lineal lemmas.

lemma span_inter_lineal_eq_lineal' (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  convert span_inter_face_span_inf_face ⟨_, IsFaceOf.lineal _⟩
  simp
  exact (IsFaceOf.lineal _).subset

lemma FG.lineal_fg' {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by
  convert FG.face_fg_of_fg hC ⟨_, IsFaceOf.lineal _⟩
  simp

end Field


end PointedCone
