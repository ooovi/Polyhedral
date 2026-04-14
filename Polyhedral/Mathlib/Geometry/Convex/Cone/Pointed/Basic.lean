
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

-- allows us to use dot notation for lemmas in Submodule.FG or PointedCone.FG
abbrev FG (C : PointedCone R M) : Prop := Submodule.FG C

----

set_option backward.isDefEq.respectTransparency false in
@[mono] lemma ofSubmodule_monotone : Monotone (ofSubmodule : Submodule R M → PointedCone R M) :=
  Submodule.restrictScalars_monotone ..

@[simp] lemma ofSubmodule_mono {S T : Submodule R M} : ofSubmodule S ≤ ofSubmodule T ↔ S ≤ T := by
  rfl

-- ## SPAN

def hull_gi : GaloisInsertion (hull R : Set M → PointedCone R M) (↑) where
  choice s _ := hull R s
  gc _ _ := Submodule.span_le
  le_l_u _ := subset_hull
  choice_eq _ _ := rfl

-- lemma span_inf_left (s t : Set M) : span R (s ∩ t) ≤ span R s := by
--   apply Submodule.span_mono
--   simp only [Set.inter_subset_left]


-- ## LINSPAN

/-- The linear span of the cone. -/
abbrev linSpan (C : PointedCone R M) : Submodule R M := .span R C

@[simp high] lemma ofSubmodule_linSpan (S : Submodule R M) : (S : PointedCone R M).linSpan = S :=
    by simp [linSpan]

@[deprecated (since := "today")]
alias coe_linSpan := ofSubmodule_linSpan

@[deprecated (since := "today")]
alias submodule_linSpan := ofSubmodule_linSpan

@[deprecated (since := "today")]
alias linSpan_eq := ofSubmodule_linSpan

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma linSpan_hull_eq_submodule_span (s : Set M) :
    (hull R s).linSpan = Submodule.span R s := Submodule.span_span_of_tower ..

@[deprecated (since := "today")]
alias span_submodule_span := linSpan_hull_eq_submodule_span

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

set_option backward.isDefEq.respectTransparency false in
lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  Submodule.restrictScalars_sInf _ _

lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

-- lemma iInf_coe' (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
--   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf]

set_option backward.isDefEq.respectTransparency false in
lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M)
    := Submodule.restrictScalars_sup _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  Submodule.restrictScalars_sSup _ _

lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]


-- ## SPAN

-- /-- The submodule span of a finitely generated pointed cone is finitely generated. -/
-- lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span (M := M) R C).FG := by
--   obtain ⟨s, rfl⟩ := hC; use s; simp

-- TODO: this is only needed because `Submodule.span_insert` is restricted to rings
--@[deprecated "Really needed?" (since := "today")]
lemma hull_insert (x) (s : Set M) : hull R (insert x s) = hull R {x} ⊔ hull R s :=
  Submodule.span_insert x s

lemma coe_sup_submodule_span' {s t : Set M} :
    Submodule.span R (s ∪ t) = Submodule.span R (hull R s ⊔ hull R t) := by simp

-- Has this anything to do with cones? See version above
lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ∪ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  rw [← linSpan_hull_eq_submodule_span]
  simp [Submodule.span_union]

set_option backward.isDefEq.respectTransparency false in
lemma hull_le_submodule_span (s : Set M) : hull R s ≤ Submodule.span R s :=
    Submodule.span_le_restrictScalars _ _ s

@[deprecated "We don't need this, the proof is short" (since := "today")]
lemma hull_le_submodule_span_of_le {s t : Set M} (hst : s ⊆ t) : hull R s ≤ Submodule.span R t
  := le_trans (hull_le_submodule_span s) (Submodule.span_mono hst)

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
lemma submodule_span_of_hull {s : Set M} {S : Submodule R M} (hsS : hull R s = S) :
    Submodule.span R s = S := by
  simpa using congrArg (Submodule.span R ∘ SetLike.coe) hsS

-- lemma span_eq_submodule_span {s : Set M} (h : ∃ S : Submodule R M, span R s = S) :
--     span R s = Submodule.span R s := by
--   obtain ⟨S, hS⟩ := h; rw [hS]
--   simpa using (congrArg (Submodule.span R ∘ SetLike.coe) hS).symm

lemma hull_union (s t : Set M) : hull R (s ∪ t) = hull R s ⊔ hull R t :=
    Submodule.span_union s t

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- TODO: write version with `restrictScalars` instead. (Or have I already??)
lemma sup_inf_submodule_span_of_disjoint {C : PointedCone R M} {S : Submodule R M}
  (hS : Disjoint C.linSpan S) : (C ⊔ S) ⊓ C.linSpan = C := by
  rw [sup_inf_assoc_of_le_submodule]
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

set_option backward.isDefEq.respectTransparency false in
lemma restrict_inf (S : Submodule R M) {C D : PointedCone R M} :
    (C ⊓ D).restrict S = C.restrict S ⊓ D.restrict S
  := by ext x; simp [restrict, Submodule.submoduleOf]

set_option backward.isDefEq.respectTransparency false in
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



section Ring

section PartialOrder

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Pointwise

open Pointwise

@[simp] lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

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

end Pointwise

end PartialOrder

section DirectedOrder

variable {R : Type*} [Ring R] [PartialOrder R] [IsDirectedOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

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

-- NOTE: I changed the statement of the lemma and added the `rw` to the first line that
--  transforms it into the previous statement. Maybe there is a shorter proof now?
-- TODO: simplify proof?
--
-- Mathematically, this lemma is equivalent to directedness of the order on `R`: for `M = R`
-- and `x = 1`, it says every element of `R` is a difference of two nonnegative elements.
variable (R) in
@[simp] lemma hull_neg_pair_eq_span_singleton (x : M) : hull R {-x, x} = R ∙ x := by
  rw [← Submodule.span_insert_eq_span_of_mem (Set.mem_singleton x)]
  ext y
  simp only [Submodule.restrictScalars_mem, Submodule.mem_span_pair, smul_neg, Subtype.exists]
  constructor
  · rintro ⟨a, _, b, _, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
    refine ⟨c - b, sub_nonneg.mpr hbc, c - a, sub_nonneg.mpr hac, ?_⟩
    calc
      -((c - b) • x) + (c - a) • x = (-(c - b) + (c - a)) • x := by
        rw [← neg_smul, ← add_smul]
      _ = (b - a) • x := by
        congr 1
        abel
      _ = -(a • x) + b • x := by
        rw [sub_smul]
        abel

@[simp] lemma hull_sup_hull_neg_eq_submodule_span (s : Set M) :
    hull R s ⊔ hull R (-s) = Submodule.span R s := by
  ext x
  constructor <;> intro h
  · obtain ⟨_, hy, _, hz, rfl⟩ := Submodule.mem_sup.mp h
    exact add_mem
      (Submodule.mem_span.mpr fun p hp => Submodule.mem_span.mp hy p hp)
      (Submodule.mem_span.mpr fun p hp => Submodule.mem_span.mp hz p <| by
        intro y hy
        simpa using p.neg_mem (hp (Set.mem_neg.mp hy)))
  · rw [Submodule.restrictScalars_mem, Submodule.mem_span_set'] at h
    obtain ⟨n, f, g, rfl⟩ := h
    have hx : ∑ i, f i • (g i : M) ∈ hull R (-s ∪ s) := by
      refine sum_mem ?_
      intro i _
      have hpair : f i • (g i : M) ∈ hull R ({-(g i : M), (g i : M)} : Set M) := by
        rw [hull_neg_pair_eq_span_singleton (R := R) (x := (g i : M))]
        exact Submodule.mem_span_singleton.mpr ⟨f i, by simp⟩
      exact Set.mem_of_subset_of_mem (Submodule.span_mono <| by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact Set.mem_union_left _ (by simp [(g i).property])
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact Set.mem_union_right _ (g i).property) hpair
    simpa [hull_union, sup_comm, Set.union_comm] using hx

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointed cones. Especially the proof that R≥0 is an FG
-- submodule of R should be easier with this.
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma hull_union_neg_eq_submodule_span (s : Set M) :
    hull R (-s ∪ s) = Submodule.span R s := by
  ext x
  simp only [Submodule.mem_span, Set.union_subset_iff, and_imp,
    Submodule.restrictScalars_mem]
  constructor <;> intros h B sB
  · refine h (B.restrictScalars _) ?_ sB
    rw [Submodule.coe_restrictScalars]
    exact fun _ tm => neg_mem_iff.mp (sB tm)
  · intro nsB
    have : x ∈ (Submodule.span R s : PointedCone R M) :=
      h (Submodule.span R s) Submodule.subset_span
    rw [← hull_sup_hull_neg_eq_submodule_span] at this
    obtain ⟨_, h₁, _, h₂, h⟩ := Submodule.mem_sup.mp this
    rw [← h]
    apply add_mem
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr nsB) h₁
    · exact Set.mem_of_subset_of_mem (Submodule.span_le.mpr sB) h₂

lemma hull_eq_submodule_span_of_neg_self {s : Set M} (hs : s = -s) :
    hull R s = Submodule.span R s := by
  nth_rw 1 [← Set.union_self s, hs]
  exact hull_union_neg_eq_submodule_span s

section Pointwise

open Pointwise

lemma sup_neg_eq_linSpan (C : PointedCone R M) : -C ⊔ C = C.linSpan := by
  nth_rw 1 2 [← Submodule.span_eq C]
  rw [← Submodule.span_neg_eq_neg, ← Submodule.span_union]
  exact hull_union_neg_eq_submodule_span (C : Set M)

-- NOTE: I think only one of `neg_eq_iff_eq_linSpan` and `neg_eq_iff_eq_linSpan` is needed.
--  I don't know which.

lemma neg_eq_iff_eq_linSpan {C : PointedCone R M} : -C = C ↔ C.linSpan = C := by
  rw [← sup_neg_eq_linSpan, sup_eq_right]
  exact Submodule.neg_eq_self_iff_neg_le

lemma neg_le_iff_eq_linSpan {C : PointedCone R M} : -C ≤ C ↔ C.linSpan = C :=
  Iff.trans Submodule.neg_eq_self_iff_neg_le.symm neg_eq_iff_eq_linSpan

end Pointwise

lemma mem_linSpan {C : PointedCone R M} {x : M} :
    x ∈ C.linSpan ↔ ∃ p ∈ C, ∃ n ∈ C, p = x + n := by
  rw [← mem_ofSubmodule_iff, ← sup_neg_eq_linSpan, Submodule.mem_sup]
  simp only [Submodule.mem_neg]
  constructor <;> intro h
  · obtain ⟨y, hy', z, hz, rfl⟩ := h
    exact ⟨z, hz, -y, hy', by simp⟩
  · obtain ⟨p, hp, n, hn, rfl⟩ := h
    exact ⟨-n, by simp [hn], x + n, hp, by simp⟩

end DirectedOrder

section PartialOrder

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

end PartialOrder

section LinearOrder

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_hull (f : M →ₗ[R] M') (s : Set M) : map f (hull R s) = hull R (f '' s) :=
  Submodule.map_span _ _

end Map

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

end LinearOrder

end Ring


-- # QUOTIENTS

/- Most, if not everything, from this section should be proven for general restricted scalars. -/

section Quotient

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

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

/-- The linear span of a quotient cone is the image of the linear span under the quotient map. -/
@[simp] lemma linSpan_quot (C : PointedCone R M) (S : Submodule R M) :
    (C.quot S).linSpan = Submodule.map S.mkQ C.linSpan := by
  simpa [PointedCone.quot, PointedCone.linSpan] using
    (Submodule.span_image (f := S.mkQ) (s := (C : Set M)))

@[simp] lemma sup_quot_eq_quot (C : PointedCone R M) (S : Submodule R M) :
    (C ⊔ S).quot S = C.quot S := sorry


set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma quot_eq_iff_sup_eq {S : Submodule R M} {C D : PointedCone R M} :
    C.quot S = D.quot S ↔ C ⊔ S = D ⊔ S := Submodule.map_mkQ_eq_iff_sup_eq

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma map_mkQ_le_iff_sup_le {p : Submodule R M} {s t : PointedCone R M} :
    map p.mkQ s ≤ map p.mkQ t ↔ s ⊔ p ≤ t ⊔ p := Submodule.map_mkQ_le_iff_sup_le

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma map_mkQ_eq_iff_sup_eq {p : Submodule R M} {s t : PointedCone R M} :
    map p.mkQ s = map p.mkQ t ↔ s ⊔ p = t ⊔ p := Submodule.map_mkQ_eq_iff_sup_eq

section CommRing

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

local notation "R≥0" => {c : R // 0 ≤ c}

set_option backward.isDefEq.respectTransparency false in
noncomputable def IsCompl.map_mkQ_equiv_inf {S T : Submodule R M} (hST : IsCompl S T)
    {C : PointedCone R M} (hSC : S ≤ C) : C.quot S ≃ₗ[R≥0] (C ⊓ T : PointedCone R M) :=
  Submodule.IsCompl.map_mkQ_equiv_inf hST hSC

end CommRing

end Quotient

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
set_option backward.isDefEq.respectTransparency false in
theorem hull_singleton_smul_eq {r : R} (hr : r > 0) (x : M) : hull R {r • x} = hull R {x} := by
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

end PointedCone
