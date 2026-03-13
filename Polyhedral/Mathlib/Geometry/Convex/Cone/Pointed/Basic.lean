
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Cardinal.Defs

import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual

namespace PointedCone

open Module Function

section CommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

local notation "R≥0" => {c : R // 0 ≤ c}

instance : Algebra R≥0 R where
  algebraMap := Nonneg.coeRingHom
  commutes' r x := mul_comm ..
  smul_def' r x := by aesop

example : CommSemiring R≥0 := inferInstance

end CommSemiring

section Semiring

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M] {S : Set M}

@[coe]
abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

instance : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

@[simp]
lemma ofSubmodule_coe (S : Submodule R M) : (ofSubmodule S : Set M) = S := by rfl
  -- also provable from `Submodule.coe_restrictScalars R S`

@[simp]
lemma mem_coe {S : Submodule R M} {x : M} : x ∈ (S : PointedCone R M) ↔ x ∈ S := by rfl
  -- also provable from `Submodule.coe_restrictScalars R S`

alias ofSubmodule_toSet_coe := ofSubmodule_coe

@[simp] lemma ofSubmodule_inj {S T : Submodule R M} : ofSubmodule S = ofSubmodule T ↔ S = T
  := Submodule.restrictScalars_inj ..

def ofSubmodule_embedding : Submodule R M ↪o PointedCone R M :=
  Submodule.restrictScalarsEmbedding ..

def ofSubmodule_latticeHom : CompleteLatticeHom (Submodule R M) (PointedCone R M) :=
  Submodule.restrictScalarsLatticeHom ..

lemma ofSubmodule_sInf (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  ofSubmodule_latticeHom.map_sInf' s

lemma ofSubmodule_sSup (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  ofSubmodule_latticeHom.map_sSup' s

-- ## SPAN

/- Intended new name for `PointedCone.span` to better avoid name clashes and confusion
  with `Submodule.span`. -/
alias hull := span

@[simp] lemma span_submodule_span (s : Set M) :
    Submodule.span R (span R s) = Submodule.span R s := Submodule.span_span_of_tower ..

def span_gi : GaloisInsertion (span R : Set M → PointedCone R M) (↑) where
  choice s _ := span R s
  gc _ _ := Submodule.span_le
  le_l_u _ := subset_span
  choice_eq _ _ := rfl

-- lemma span_inf_left (s t : Set M) : span R (s ∩ t) ≤ span R s := by
--   apply Submodule.span_mono
--   simp only [Set.inter_subset_left]


-- ## LINSPAN

/-- The linear span of the cone. -/
abbrev linSpan (C : PointedCone R M) : Submodule R M := .span R C

@[simp] lemma coe_linSpan (S : Submodule R M) : (S : PointedCone R M).linSpan = S :=
    by simp [linSpan]

@[deprecated (since := "today")]
alias submodule_linSpan := coe_linSpan

@[deprecated (since := "today")]
alias linSpan_eq := coe_linSpan

-- section Ring

-- variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
--   [Module R M] {S : Set M}

-- lemma exists_sub_of_mem_linSpan (C : PointedCone R M) {x : M} (h : x ∈ C.linSpan) :
--     ∃ xp ∈ C, ∃ xm ∈ C, xp - xm = x := sorry

-- end Ring


end Semiring


-- ## COE

section Semiring_AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf _ _ _

lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  Submodule.restrictScalars_sInf _ _

lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

-- lemma iInf_coe' (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
--   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf]

lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M)
    := Submodule.restrictScalars_sup _ _ _

lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  Submodule.restrictScalars_sSup _ _

lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]


-- ## SPAN

-- /-- The submodule span of a finitely generated pointed cone is finitely generated. -/
-- lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span (M := M) R C).FG := by
--   obtain ⟨s, rfl⟩ := hC; use s; simp

@[deprecated "Really needed?" (since := "today")]
lemma span_insert (x) (s : Set M) : span R (insert x s) = span R {x} ⊔ span R s :=
  Submodule.span_insert x s

lemma coe_sup_submodule_span' {s t : Set M} :
    Submodule.span R (s ∪ t) = Submodule.span R (span R s ⊔ span R t) := by simp

-- Has this anything to do with cones? See version above
lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ∪ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  rw [← span_submodule_span]
  simp [Submodule.span_union]

lemma span_le_submodule_span (s : Set M) : span R s ≤ Submodule.span R s :=
    Submodule.span_le_restrictScalars _ _ s

@[deprecated "We don't need this, the proof is short" (since := "today")]
lemma span_le_submodule_span_of_le {s t : Set M} (hst : s ⊆ t) : span R s ≤ Submodule.span R t
  := le_trans (span_le_submodule_span s) (Submodule.span_mono hst)

lemma le_linSpan (C : PointedCone R M) : C ≤ C.linSpan := Submodule.subset_span

@[deprecated (since := "today")]
alias le_submodule_span_self := le_linSpan

@[deprecated (since := "today")]
alias le_submodule_span := le_linSpan

@[deprecated "We don't need this, the proof is short" (since := "today")]
lemma le_submodule_span_of_le {C D : PointedCone R M} (hCD : C ≤ D) : C ≤ D.linSpan :=
  le_trans hCD (le_linSpan D)

@[deprecated (since := "today")]
alias le_span := subset_span

-- should be in `Submodule.Basic`
@[deprecated "Really needed?" (since := "today")]
lemma submodule_span_of_span {s : Set M} {S : Submodule R M} (hsS : span R s = S) :
    Submodule.span R s = S := by
  simpa using congrArg (Submodule.span R ∘ SetLike.coe) hsS

-- lemma span_eq_submodule_span {s : Set M} (h : ∃ S : Submodule R M, span R s = S) :
--     span R s = Submodule.span R s := by
--   obtain ⟨S, hS⟩ := h; rw [hS]
--   simpa using (congrArg (Submodule.span R ∘ SetLike.coe) hS).symm

lemma span_union (s t : Set M) : span R (s ∪ t) = span R s ⊔ span R t :=
    Submodule.span_union s t

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma sup_inf_assoc_of_le_submodule {C : PointedCone R M} (D : PointedCone R M)
    {S : Submodule R M} (hCS : C ≤ S) : C ⊔ (D ⊓ S) = (C ⊔ D) ⊓ S :=
  Submodule.sup_inf_assoc_of_le_restrictScalars D hCS

lemma inf_sup_assoc_of_submodule_le {C : PointedCone R M} (D : PointedCone R M)
    {S : Submodule R M} (hSC : S ≤ C) : C ⊓ (D ⊔ S) = (C ⊓ D) ⊔ S :=
  Submodule.inf_sup_assoc_of_restrictScalars_le D hSC

-- TODO: write version with `restrictScalars` instead. (Or have I already??)
lemma sup_inf_submodule_span_of_disjoint {C : PointedCone R M} {S : Submodule R M}
  (hS : Disjoint C.linSpan S) : (C ⊔ S) ⊓ C.linSpan = C := by
  rw [← sup_inf_assoc_of_le_submodule]
  · rw [inf_comm, ← coe_inf, disjoint_iff.mp hS]; simp
  · exact le_linSpan C

end Ring

--------------------------

-- ## RESTRICT / EMBED

-- TODO: move to a separate file Restrict.lean like we did for submodules

/- TODO: generalize these restrict/embed lemmas to general case where we restrict a
  restrictScalar subspace to a normal subspace. -/

-- TODO: generalize to restrict using restrictScalar, so we can need to write only one instead
--  of two for submodules and pointed cones.

-- Q: Do we maybe want notation for this? For example: `S ⊓ᵣ C`?
/-- The intersection `C ⊓ S` considered as a cone in `S`. -/
abbrev restrict (S : Submodule R M) (C : PointedCone R M) : PointedCone R S
  := C.submoduleOf S -- C.comap S.subtype

-- alias pointedConeOf := restrict

-- @[simp]
lemma coe_restrict (S T : Submodule R M) :
    restrict S T = Submodule.restrict S T := by
  unfold restrict Submodule.restrict Submodule.submoduleOf
  sorry

lemma restrict_eq_comap_subtype (S : Submodule R M) (T : PointedCone R M) :
    restrict S T = comap S.subtype T := rfl

-- @[simp] lemma restrict_top (S : Submodule R M) : restrict S ⊤ = ⊤ := Submodule.restrict_top _
-- @[simp] lemma restrict_bot (S : Submodule R M) : restrict S ⊥ = ⊥ := Submodule.restrict_bot _

-- @[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := Submodule.restrict_self _

lemma mem_restrict {S : Submodule R M} {T : PointedCone R M} {x : S} (h : x ∈ restrict S T) :
    (x : M) ∈ T := by simpa only using h

lemma mem_restrict_iff {S : Submodule R M} {T : PointedCone R M} {x : S} :
    x ∈ restrict S T ↔ (x : M) ∈ T := ⟨mem_restrict, (by simpa using ·)⟩

/-- A cone `C` in a submodule `S` of `M` intepreted as a cone in `M`. -/
@[coe] abbrev embed {S : Submodule R M} (C : PointedCone R S) : PointedCone R M := C.map S.subtype

lemma embed_injective {S : Submodule R M} : Injective (embed : PointedCone R S → PointedCone R M)
  := Submodule.map_injective_of_injective S.subtype_injective

@[simp] lemma embed_inj {S : Submodule R M} {T₁ T₂ : PointedCone R S} :
    embed T₁ = embed T₂ ↔ T₁ = T₂ := Injective.eq_iff embed_injective

-- TODO: use `Monotone`
lemma embed_mono {S : Submodule R M} {C₁ C₂ : PointedCone R S} (hT : C₁ ≤ C₂) :
    embed C₁ ≤ embed C₂ := Submodule.map_mono hT

lemma embed_mono_rev {S : Submodule R M} {C₁ C₂ : PointedCone R S} (hC : embed C₁ ≤ embed C₂) :
    C₁ ≤ C₂ := (by simpa using @hC ·)

@[simp] lemma embed_mono_iff {S : Submodule R M} {C₁ C₂ : PointedCone R S} :
    embed C₁ ≤ embed C₂ ↔ C₁ ≤ C₂ where
  mp := embed_mono_rev
  mpr := embed_mono

-- this should have higher priority than `map_top`
@[simp] lemma embed_top {S : Submodule R M} : embed (⊤ : PointedCone R S) = S := by sorry
@[simp] lemma embed_bot {S : Submodule R M} : embed (⊥ : PointedCone R S) = ⊥ := by sorry

@[simp] lemma embed_le {S : Submodule R M} {C : PointedCone R S} : embed C ≤ S := by sorry

@[simp] lemma embed_restrict (S : Submodule R M) (C : PointedCone R M) :
    (C.restrict S).embed = (S ⊓ C : PointedCone R M) := by
  -- unfold embed restrict map comap
  -- -- rw [← Submodule.restrictScalars_]
  -- --rw [Submodule.restrictScalars_s]
  -- --rw [comap_restrictScalar]
  -- rw [← Submodule.restrictScalars_map]
  -- exact Submodule.map_comap_subtype
  sorry -- map_comap_subtype _ _

@[simp]
lemma restrict_embed (S : Submodule R M) (C : PointedCone R S) : restrict S (embed C) = C
  := by sorry -- simp [restrict, embed, pointedConeOf, submoduleOf, map, comap_map_eq]

lemma embed_fg_of_fg (S : Submodule R M) {C : PointedCone R S} (hC : C.FG) :
    C.embed.FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {C : PointedCone R S} (hC : C.embed.FG) : C.FG
    := Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype (S : PointedCone R M)) hC

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {C : PointedCone R S} : C.embed.FG ↔ C.FG
  := ⟨fg_of_embed_fg, embed_fg_of_fg S⟩

lemma restrict_fg_of_fg_le {S : Submodule R M} {C : PointedCone R M} (hSC : C ≤ S) (hC : C.FG) :
    (C.restrict S).FG := by
  rw [← (inf_eq_left.mpr hSC), inf_comm, ← embed_restrict] at hC
  exact fg_of_embed_fg hC

lemma fg_of_restrict_le {S : Submodule R M} {C : PointedCone R M}
    (hSC : C ≤ S) (hC : (C.restrict S).FG) : C.FG := by
  rw [← (inf_eq_left.mpr hSC), inf_comm, ← embed_restrict]
  exact embed_fg_of_fg S hC

@[simp] lemma fg_iff_restrict_le {S : Submodule R M} {C : PointedCone R M} (hSC : C ≤ S) :
    (C.restrict S).FG ↔ C.FG := ⟨fg_of_restrict_le hSC, restrict_fg_of_fg_le hSC⟩

lemma restrict_fg_iff_inf_fg (S : Submodule R M) (C : PointedCone R M) :
    (C.restrict S).FG ↔ (S ⊓ C : PointedCone R M).FG := by
  rw [← embed_restrict, embed_fg_iff_fg]

lemma restrict_mono (S : Submodule R M) {C D : PointedCone R M} (hCD : C ≤ D) :
    C.restrict S ≤ D.restrict S := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {C D : PointedCone R M} :
    (C ⊓ D).restrict S = C.restrict S ⊓ D.restrict S
  := by ext x; simp [restrict, Submodule.submoduleOf]

@[simp]
lemma restrict_inf_submodule (S : Submodule R M) (C : PointedCone R M) :
    (C ⊓ S).restrict S = C.restrict S := by
  simp [restrict_inf, Submodule.restrict_self]

@[simp]
lemma restrict_submodule_inf (S : Submodule R M) (C : PointedCone R M) :
    (S ⊓ C : PointedCone R M).restrict S = C.restrict S := by simp

-- lemma foo (S : Submodule R M) {T : Submodule R M} {C : PointedCone R M} (hCT : C ≤ T):
--   restrict (.restrict T S) (restrict T C) = restrict T (restrict S C) := sorry

-- Submodule.submoduleOf_sup_of_le

end Semiring_AddCommGroup

section RingPartialOrder

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- This lemma is used in Faces/Basic.lean. It should probably be moved there.
open Submodule in
lemma uniq_decomp_of_zero_inter {C D : PointedCone R M} {xC xD yC yD : M}
    (mxc : xC ∈ C) (myc : yC ∈ C) (mxd : xD ∈ D) (myd : yD ∈ D)
    (hCD : Disjoint C.linSpan D.linSpan)
    (s : xC + xD = yC + yD) :
    xC = yC ∧ xD = yD := by
  let sub_mem_span {C : PointedCone R M} {x y} (mx : x ∈ C) (my : y ∈ C) :=
    C.linSpan.sub_mem (mem_span_of_mem my) (mem_span_of_mem mx)
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

end RingPartialOrder

section LinearOrderRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_span (f : M →ₗ[R] M') (s : Set M) : map f (span R s) = span R (f '' s) :=
  Submodule.map_span _ _

end Map

end LinearOrderRing



-- -- ## LINEAR EQUIV

-- variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
-- variable {M : Type*} [AddCommGroup M] [Module R M]
-- variable {N : Type*} [AddCommGroup N] [Module R N]

-- local notation "R≥0" => {c : R // 0 ≤ c}

-- noncomputable def IsCompl.map_mkQ_equiv_inf {S T : Submodule R M} (hST : IsCompl S T)
--     {C : PointedCone R M} (hSC : S ≤ C) : map S.mkQ C ≃ₗ[R≥0] (C ⊓ T : PointedCone R M) :=
--   Submodule.IsCompl.map_mkQ_equiv_inf hST hSC

-- structure LinearlyEquiv (s : Set M) (t : Set N) where
--   toFun : M →ₗ[R] N
--   toInv : N →ₗ[R] M
--   inv_fun : ∀ x ∈ s, toInv (toFun x) = x
--   fun_inv : ∀ x ∈ t, toFun (toInv x) = x
-- example (S : PointedCone R M) (T : PointedCone R N) : S ≃ₗ[R≥0] T := sorry

section Ring_LinearOrder

-- we have LinearOrder because then Module.Finite { c // 0 ≤ c } R
variable {R M : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

lemma ofSubmodule_fg_of_fg {S : Submodule R M} (hS : S.FG) : (S : PointedCone R M).FG
    := Submodule.FG.restrictScalars hS

/- We current struggle to implement the converse, see `FG.of_restrictScalars`. -/
alias coe_fg := ofSubmodule_fg_of_fg

-- Q: is this problematic?
instance {S : Submodule R M} : Coe S.FG (S : PointedCone R M).FG := ⟨coe_fg⟩

@[simp]
lemma coe_fg_iff {S : Submodule R M} : (S : PointedCone R M).FG ↔ S.FG :=
  ⟨Submodule.FG.of_restrictScalars _, coe_fg⟩

/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span R (C : Set M)).FG :=
  hC.span

/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma FG.linSpan_fg {C : PointedCone R M} (hC : C.FG) : C.linSpan.FG :=
  hC.span

@[deprecated submodule_span_fg (since := "...")]
alias span_fg := submodule_span_fg

lemma fg_top [Module.Finite R M] : (⊤ : PointedCone R M).FG :=
  ofSubmodule_fg_of_fg Module.Finite.fg_top

end Ring_LinearOrder


-- # QUOTIENTS

/- Most, if not everything, from this section should be proven for general restricted scalars. -/

section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

variable {C : PointedCone R M}

/-- The quotient of a cone along a submodule. -/
abbrev quot (C : PointedCone R M) (S : Submodule R M) : PointedCone R (M ⧸ S) := C.map S.mkQ

lemma quot_def (C : PointedCone R M) (S : Submodule R M) : C.quot S = C.map S.mkQ := rfl

lemma quot_bot_of_le {S : Submodule R M} (h : C ≤ S) : C.quot S = ⊥ := sorry

lemma quot_span : C.quot (.span R C) = ⊥ := quot_bot_of_le Submodule.le_span

lemma quot_fg (hC : C.FG) (S : Submodule R M) : (C.quot S).FG := hC.map _

/-- The linear span of a quotient cone is the image of the linear span under the quotient map. -/
@[simp] lemma linSpan_quot (C : PointedCone R M) (S : Submodule R M) :
    (C.quot S).linSpan = Submodule.map S.mkQ C.linSpan := by
  simpa [PointedCone.quot, PointedCone.linSpan] using
    (Submodule.span_image (f := S.mkQ) (s := (C : Set M)))

@[simp] lemma sup_quot_eq_quot (C : PointedCone R M) (S : Submodule R M) :
    (C ⊔ S).quot S = C.quot S := sorry


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

end Ring

section DivisionRing

variable {R M : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

-- TODO: golf this
theorem smul_mem_iff {C : PointedCone R M} {c : R} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C := by
  constructor <;> intro h
  · have h := C.smul_mem (le_of_lt <| inv_pos.mpr hc) h
    rw [inv_smul_smul₀ (ne_of_lt hc).symm] at h
    exact h
  · exact C.smul_mem (le_of_lt hc) h

-- analogue of `Submodule.span_singleton_smul_eq`
theorem span_singleton_smul_eq {r : R} (hr : r > 0) (x : M) : span R {r • x} = span R {x} := by
  ext y
  simp [Submodule.mem_span_singleton]
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
end PointedCone
