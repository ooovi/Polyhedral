
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

@[simp] lemma submodule_linSpan (S : Submodule R M) : (S : PointedCone R M).linSpan = S :=
    by simp [linSpan]

alias linSpan_eq := submodule_linSpan

-- section Ring

-- variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
--   [Module R M] {S : Set M}

-- lemma exists_sub_of_mem_linSpan (C : PointedCone R M) {x : M} (h : x ∈ C.linSpan) :
--     ∃ xp ∈ C, ∃ xm ∈ C, xp - xm = x := sorry

-- end Ring


-- ## RANK

open Cardinal

noncomputable abbrev rank (C : PointedCone R M) := Module.rank R C.linSpan
-- ⨆ ι : { s : Set M // LinearIndepOn R id s }, (#ι.1)

lemma rank_mono {C F : PointedCone R M} (hF : F ≤ C) : F.rank ≤ C.rank :=
  Submodule.rank_mono <| Submodule.span_mono <| IsConcreteLE.coe_subset_coe'.mpr hF

noncomputable abbrev finrank (C : PointedCone R M) := Module.finrank R C.linSpan

-- NOTE: this is not the same as Module.Finite or FG!
abbrev FinRank (C : PointedCone R M) := C.linSpan.FG

lemma finRank_of_fg {C : PointedCone R M} (hC : C.FG) : C.FinRank := by
  sorry

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

theorem span_insert (x) (s : Set M) : span R (insert x s) = span R {x} ⊔ span R s :=
  Submodule.span_insert x s

lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ∪ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  rw [← span_submodule_span]
  simp [Submodule.span_union]

lemma span_le_submodule_span_of_le {s t : Set M} (hst : s ⊆ t) : span R s ≤ Submodule.span R t
  := le_trans (Submodule.span_le_restrictScalars _ R s) (Submodule.span_mono hst)

lemma span_le_submodule_span (s : Set M) : span R s ≤ Submodule.span R s
  := span_le_submodule_span_of_le (subset_refl s)

lemma le_submodule_span_of_le {C D : PointedCone R M} (hCD : C ≤ D) :
    C ≤ Submodule.span R (D : Set M) := by
  nth_rw 1 [← Submodule.span_eq C]
  exact span_le_submodule_span_of_le hCD

lemma le_submodule_span (C : PointedCone R M) : C ≤ Submodule.span R (C : Set M)
  := le_submodule_span_of_le (le_refl C)

@[deprecated le_submodule_span (since := "")]
alias le_submodule_span_self := le_submodule_span

alias le_span := subset_span

-- should be in `Submodule.Basic`
lemma submodule_span_of_span {s : Set M} {S : Submodule R M} (hsS : span R s = S) :
    Submodule.span R s = S := by
  simpa using congrArg (Submodule.span R ∘ SetLike.coe) hsS

lemma span_eq_submodule_span {s : Set M} (h : ∃ S : Submodule R M, span R s = S) :
    span R s = Submodule.span R s := by
  obtain ⟨S, hS⟩ := h; rw [hS]
  simpa using (congrArg (Submodule.span R ∘ SetLike.coe) hS).symm

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

-- TODO: write version with `restrictScalars` instead.
lemma sup_inf_submodule_span_of_disjoint {C : PointedCone R M} {S : Submodule R M}
  (hS : Disjoint (Submodule.span R C) S) : (C ⊔ S) ⊓ Submodule.span R (C : Set M) = C := by
  rw [← sup_inf_assoc_of_le_submodule]
  · rw [inf_comm, ← coe_inf, disjoint_iff.mp hS]; simp
  · exact le_submodule_span C

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



-- ### NEG

instance : InvolutiveNeg (PointedCone R M) := Submodule.involutivePointwiseNeg -- ⟨map (f := -.id)⟩

/- The following lemmas are now automatic. -/
-- lemma neg_neg (P : PointedCone R M) : - -P = P := by simp
-- lemma neg_coe {P : PointedCone R M} : (-P : PointedCone R M) = -(P : Set M) := by simp
-- lemma mem_neg {x : M} {P : PointedCone R M} : x ∈ -P ↔ -x ∈ P := by simp
-- lemma neg_mem_neg {x : M} {P : PointedCone R M} : -x ∈ -P ↔ x ∈ P := by simp
-- lemma neg_inj {P Q : PointedCone R M} : -P = -Q ↔ P = Q := by simp
-- lemma span_neg_eq_neg {s : Set M} : span R (-s) = -(span R s) := Submodule.span_neg_eq_neg s
-- lemma neg_inf {P Q : PointedCone R M} : -(P ⊓ Q) = -P ⊓ -Q := by simp
-- lemma neg_sup {P Q : PointedCone R M} : -(P ⊔ Q) = -P ⊔ -Q := by simp
-- lemma neg_top : -⊤ = (⊤ : PointedCone R M) := by simp
-- lemma neg_bot : -⊥ = (⊥ : PointedCone R M) := by simp

-- TODO: Does this not already exist?
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
  simp
  constructor <;> {
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨-x, by simpa [neg_eq_iff_eq_neg] using hx⟩
  }

lemma comap_neg (C : PointedCone R M) (f : N →ₗ[R] M) : comap (-f) C = comap f (-C) := by
  ext x; simp

lemma comap_neg_apply (C : PointedCone R M) (f : N →ₗ[R] M) : -comap f C = comap f (-C) := by
  ext x; simp

end Semiring_AddCommGroup

section RingPartialOrder

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- This lemma is used in Faces/Basic.lean. It should probably be moved there.
open Submodule in
lemma uniq_decomp_of_zero_inter {C D : PointedCone R M} {xC xD yC yD : M}
    (mxc : xC ∈ C) (myc : yC ∈ C) (mxd : xD ∈ D) (myd : yD ∈ D)
    (hCD : Disjoint (Submodule.span R C) (Submodule.span (M := M) R D))
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

end RingPartialOrder

section Ring

-- variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simp]
lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

-- lemma neg_self_iff_eq_span_submodule {C : PointedCone R M} (hC : -C = C) :
--     Submodule.span R (C : Set M) = C := by
--   suffices h : ∀ C, Submodule.span R (C : Set M) ≥ C from by
--     rw [le_antisymm_iff]
--     constructor
--     · rw [← Submodule.neg_le_neg]
--       sorry
--     · exact h C
--   intro C
--   exact Submodule.subset_span

-- lemma foo {α : Type} [InvolutiveNeg α] [SupSet α] (s : Set α) :
--     ⨆ a ∈ s ⊔ -s, a = ⨆ a ∈ α × FinSet 2,  := by sorry

-- lemma foo (s : Set (PointedCone R M)) :
--     ⨆ C ∈ s ⊔ -s, C = ⨆ C ∈ s, (C ⊔ -C) := by
--   simp
--   rw [le_antisymm_iff]
--   constructor
--   · intro h

--     sorry
--   · sorry

-- Does this theorem need linear order (as opposed to a partial order)?
-- If not, then neither a lot of things downstream.
variable (R) in
lemma span_pm_pair_eq_submodule_span (x : M) :
    span R {-x, x} = Submodule.span R {-x, x} := by
  ext y
  simp only [Submodule.restrictScalars_mem, Submodule.mem_span_pair,
    smul_neg, Subtype.exists, Nonneg.mk_smul, exists_prop, ← neg_smul, ← add_smul]
  constructor
  · intro h
    obtain ⟨a, _, b, _, h⟩ := h
    exact ⟨a, b, h⟩
  · intro h
    obtain ⟨a, b, h⟩ := h
    by_cases H : -a + b ≥ 0
    · exact ⟨0, le_refl 0, _, H, by simp [h]⟩
    · exact ⟨-b + a, by
        simp_all only [ge_iff_le, le_neg_add_iff_add_le, add_zero, not_le]
        exact le_of_lt H, 0, le_refl 0, by simp [h]⟩

-- TODO: move to Submodule/Basic
omit [IsOrderedRing R] [LinearOrder R] in
variable (R) in
@[simp] lemma submodule_span_pm_pair (x : M) :
    Submodule.span R {-x, x} = Submodule.span R {x} := by
  rw [← Set.union_singleton, Submodule.span_union]; simp

variable (R) in
lemma span_sign_pair_eq_submodule_span_singleton (x : M) :
    span R {-x, x} = Submodule.span R {x} := by
  simpa [← submodule_span_pm_pair] using span_pm_pair_eq_submodule_span R x

lemma submodule_span_eq_add_span_neg (s : Set M) : Submodule.span R s = span R s ⊔ span R (-s) := by
  ext x; constructor <;> intros h
  · simp only [Submodule.restrictScalars_mem, Submodule.mem_span_set'] at h
    obtain ⟨_, f, g, h⟩ := h
    simp only [Set.involutiveNeg, Submodule.mem_sup]
    rw[← h, ← Finset.sum_filter_add_sum_filter_not _ (fun i => 0 ≤ f i)]
    use ∑ x with 0 ≤ f x, f x • g x
    simp only [not_le, add_right_inj, exists_eq_right]
    constructor <;> apply sum_mem
    · exact fun x xm => smul_mem _ ((Finset.mem_filter.mp xm).2) (subset_span (g x).property)
    · intros x xm
      rw [← neg_smul_neg]
      apply smul_mem
      · exact Left.nonneg_neg_iff.mpr (le_of_lt (Finset.mem_filter.mp xm).2)
      · apply subset_span
        simp
  · simp_all [Submodule.mem_sup]
    obtain ⟨_, hy, _, hz, h⟩ := h
    rw [← h]
    apply add_mem
    · exact Submodule.mem_span.mpr (fun p hp => Submodule.mem_span.mp hy p hp)
    · refine Submodule.mem_span.mpr (fun p hp => Submodule.mem_span.mp hz p ?_)
      intro x xs
      convert p.neg_mem <| hp <| Set.mem_neg.mp xs
      exact (InvolutiveNeg.neg_neg x).symm

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointed cones. Especially the proof that R≥0 is an FG
-- submodule of R should be easier with this.
lemma span_union_neg_eq_span_submodule (s : Set M) :
    span R (-s ∪ s) = Submodule.span R s := by
  ext x
  simp only [Set.involutiveNeg, Submodule.mem_span, Set.union_subset_iff, and_imp,
    Submodule.restrictScalars_mem]
  constructor <;> intros h B sB
  · refine h (Submodule.restrictScalars {c : R // 0 ≤ c} B) ?_ sB
    rw [Submodule.coe_restrictScalars]
    exact fun _ tm => neg_mem_iff.mp (sB tm)
  · intro nsB
    have : x ∈ (Submodule.span R s : PointedCone R M) :=
      h (Submodule.span R s) Submodule.subset_span
    rw [submodule_span_eq_add_span_neg s] at this
    obtain ⟨_, h₁, _, h₂, h⟩ := Submodule.mem_sup.mp this
    rw [← h]
    apply add_mem
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr nsB) h₁
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr sB) h₂

lemma sup_neg_eq_submodule_span (C : PointedCone R M) :
    -C ⊔ C = Submodule.span R (C : Set M) := by
  nth_rw 1 2 [← Submodule.span_eq C]
  rw [← Submodule.span_neg_eq_neg, ← Submodule.span_union]
  exact span_union_neg_eq_span_submodule (C : Set M)

lemma span_eq_submodule_span_of_neg_self {s : Set M} (hs : s = -s) :
    span R s = Submodule.span R s := by
  nth_rw 1 [← Set.union_self s]
  nth_rw 1 [hs]
  exact span_union_neg_eq_span_submodule s

lemma neg_le_iff_neg_eq {C : PointedCone R M} : -C ≤ C ↔ -C = C  where
  mp := by
    intro h
    ext x; rw [Submodule.mem_neg]
    suffices h : ∀ x, -x ∈ C → x ∈ C from by
      exact ⟨h x, by nth_rw 1 [← neg_neg x]; exact h (-x)⟩
    exact SetLike.le_def.mp @h
  mpr := le_of_eq

lemma neg_self_iff_eq_span_submodule {C : PointedCone R M} :
    -C = C ↔ Submodule.span R (C : Set M) = C := by
  rw [← sup_neg_eq_submodule_span, sup_eq_right]
  exact neg_le_iff_neg_eq.symm

lemma neg_self_iff_eq_span_submodule' {C : PointedCone R M} :
    -C ≤ C ↔ Submodule.span R (C : Set M) = C
  := Iff.trans neg_le_iff_neg_eq neg_self_iff_eq_span_submodule

lemma mem_linSpan (C : PointedCone R M) {x : M} :
    x ∈ C.linSpan ↔ ∃ p ∈ C, ∃ n ∈ C, p = x + n := by
  rw [← mem_coe, ← sup_neg_eq_submodule_span, Submodule.mem_sup]
  simp only [Submodule.mem_neg]
  constructor <;> intro h
  · obtain ⟨y, hy', z, hz, rfl⟩ := h
    exact ⟨z, hz, -y, hy', by simp⟩
  · obtain ⟨p, hp, n, hn, rfl⟩ := h
    exact ⟨-n, by simp [hn], x + n, hp, by simp⟩

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_span (f : M →ₗ[R] M') (s : Set M) : map f (span R s) = span R (f '' s) :=
  Submodule.map_span _ _

end Map

end Ring



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
