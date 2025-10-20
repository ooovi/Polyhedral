
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise

import Polyhedral.Mathlib.Algebra.Module.Submodule.FG
import Polyhedral.Mathlib.Algebra.Module.Submodule.Dual

namespace PointedCone

open Module

section Semiring

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M] {S : Set M}

-- /-- The span of a set `S` is the smallest pointed cone that contains `S`.

-- Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
-- submodule span of `S` w.r.t. nonnegative scalars. -/
-- abbrev span : PointedCone R M := Submodule.span _ S

-- lemma subset_span : S ⊆ PointedCone.span R S := Submodule.subset_span

@[coe]
abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

instance : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

lemma ofSubmodule.carrier_eq (S : Submodule R M) : (ofSubmodule S : Set M) = S :=
  Submodule.coe_restrictScalars R S

end Semiring

section Semiring_AddCommGroup

variable {R M : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [Module R M]

-- TODO: implement sSup, sInf, sSup_map, sSupHomClass and sInfHomClass also for Submodule

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf

@[simp]
lemma sSup_coe (S : Set (Submodule R M)) : sSup S = sSup (ofSubmodule '' S) := by
  ext x
  -- we would like to use something like `Submodule.restrictScalars` for `sSup`.
  -- we cannot use `map_sSup` because this needs `sSupHomClass`.
  sorry

/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span (M := M) R C).FG := by
  obtain ⟨s, rfl⟩ := hC; use s; simp

-- ### Neg

-- TODO: should be built on `Submodule.pointwiseNeg` (I realized too late that this exists)
instance : Neg (PointedCone R M) := ⟨map (f := -.id)⟩

@[simp]
lemma neg_neg (P : PointedCone R M) : - -P = P := by dsimp [Neg.neg]; ext x; simp

instance : InvolutiveNeg (PointedCone R M) where
  neg_neg := neg_neg

lemma neg_coe {P : PointedCone R M} : (-P : PointedCone R M) = -(P : Set M) := by simp [Neg.neg]

@[simp]
lemma mem_neg {x : M} {P : PointedCone R M} : x ∈ -P ↔ -x ∈ P := by
  rw [← SetLike.mem_coe, neg_coe]
  exact Set.mem_neg

-- @[simp]
-- lemma neg_mem_neg {x : M} {P : PointedCone R M} : -x ∈ -P ↔ x ∈ P := by simp

-- @[simp]
-- lemma neg_inj {P Q : PointedCone R M} : -P = -Q ↔ P = Q := _root_.neg_inj -- has simp

@[simp]
lemma span_neg {s : Set M} : -(span R s) = span R (-s) := by
  rw [← Set.image_neg_eq_neg];
  exact Submodule.map_span _ _

@[simp]
lemma neg_inf {P Q : PointedCone R M} : -(P ⊓ Q) = -P ⊓ -Q := by ext x; simp

@[simp]
lemma neg_sup {P Q : PointedCone R M} : -(P ⊔ Q) = -P ⊔ -Q := by
  sorry

@[simp]
lemma neg_top : -⊤ = (⊤ : PointedCone R M) := by ext x; simp

@[simp]
lemma neg_bot : -⊥ = (⊥ : PointedCone R M) := by ext x; simp

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointedcones. Especially the proof that R≥0 is a FG
-- submodule of R should be easiert with this.
lemma span_union_neg_eq_span_submodule {s : Set M} :
    span R (s ∪ -s) = Submodule.span R s := by
  sorry

lemma span_sup_neg_eq_span_submodule (C : PointedCone R M) :
    C ⊔ -C = Submodule.span R (C : Set M) := by
  sorry

lemma span_eq_submodule_span_of_neg_self {s : Set M} (hs : s = -s) :
    span R s = Submodule.span R s := by
  sorry

lemma neg_self_iff_eq_span_submodule (C : PointedCone R M) :
    C = -C ↔ C = Submodule.span R (C : Set M) := by
  sorry

section Map

variable {E' : Type*} [AddCommMonoid E'] [Module R E']

lemma map_span (f : M →ₗ[R] E') (s : Set M) : map f (span R s) = span R (f '' s) := by
  -- use `Submodule.map_span f s`
  sorry

end Map



end Semiring_AddCommGroup


section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M] [Module R M]

lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ⊔ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  ext x; simp; sorry

lemma span_le_submodule_span_of_le {s t : Set M} (hst : s ⊆ t) : span R s ≤ Submodule.span R t
  := le_trans (Submodule.span_le_restrictScalars _ R s) (Submodule.span_mono hst)

lemma span_le_submodule_span_self (s : Set M) : span R s ≤ Submodule.span R s
  := span_le_submodule_span_of_le (subset_refl s)

lemma le_submodule_span_of_le {C D : PointedCone R M} (hCD : C ≤ D) :
    C ≤ Submodule.span R (D : Set M) := by
  nth_rw 1 [← Submodule.span_eq C]
  exact span_le_submodule_span_of_le hCD

lemma le_submodule_span_self (C : PointedCone R M) : C ≤ Submodule.span R (C : Set M)
  := le_submodule_span_of_le (le_refl C)



lemma span_le (s : Set M) : s ≤ span R s := by sorry

--------------------------

/- TODO: generalize these restrict/embed lemmas to general case where we restrict a
  restrictScalar subspace to a normal subspace. -/

-- Q: Do we maybe want notation for this? For example: `S ⊓ᵣ T`?
/-- The intersection `C ⊓ S` considered as a cone in `S`. -/
abbrev pointedConeOf (S : Submodule R M) (C : PointedCone R M) : PointedCone R S
  := C.submoduleOf S -- C.comap S.subtype

alias restrict := pointedConeOf

-- @[simp]
lemma coe_restrict (S : Submodule R M) (T : Submodule R M) :
    restrict S T = Submodule.restrict S T := by
  sorry

/-- A cone `C` in a submodule `S` of `M` intepreted as a cone in `M`. -/
abbrev embed (S : Submodule R M) (C : PointedCone R S) : PointedCone R M := C.map S.subtype

lemma embed_restrict (S : Submodule R M) (C : PointedCone R M) :
    embed S (restrict S C) = (S ⊓ C : PointedCone R M) := by
  -- unfold embed restrict map comap
  -- -- rw [← Submodule.restrictScalars_]
  -- --rw [Submodule.restrictScalars_s]
  -- --rw [comap_restrictScalar]
  -- rw [← Submodule.restrictScalars_map]
  -- exact Submodule.map_comap_subtype
  sorry -- map_comap_subtype _ _

@[simp]
lemma restrict_embed (S : Submodule R M) (C : PointedCone R S) : restrict S (embed S C) = C
  := by sorry -- simp [restrict, embed, pointedConeOf, submoduleOf, map, comap_map_eq]

lemma embed_fg_of_fg (S : Submodule R M) {C : PointedCone R S} (hC : C.FG) :
    (C.embed S).FG := Submodule.FG.map _ hC

lemma fg_of_embed_fg {S : Submodule R M} {C : PointedCone R S} (hC : (C.embed S).FG) : C.FG
    := Submodule.fg_of_fg_map_injective _ (Submodule.injective_subtype (S : PointedCone R M)) hC

@[simp] lemma embed_fg_iff_fg {S : Submodule R M} {C : PointedCone R S} : (C.embed S).FG ↔ C.FG
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
  simp [restrict_inf, coe_restrict, Submodule.restrict_self]

@[simp]
lemma restrict_submodule_inf (S : Submodule R M) (C : PointedCone R M) :
    (S ⊓ C : PointedCone R M).restrict S = C.restrict S := by
  simp [restrict_inf, coe_restrict, Submodule.restrict_self]

-- lemma foo (S : Submodule R M) {T : Submodule R M} {C : PointedCone R M} (hCT : C ≤ T):
--   restrict (.restrict T S) (restrict T C) = restrict T (restrict S C) := sorry

-- Submodule.submoduleOf_sup_of_le


end Ring


section Ring_AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- ## Lineality

/-- The lineality space of a cone. -/
def lineal (C : PointedCone R M) : Submodule R M := sSup {S : Submodule R M | S ≤ C }

def lineal_sSup (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C } := by rfl

lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp [lineal] -- [sSup_coe]

lemma le_lineal {C : PointedCone R M} {S : Submodule R M} (hS : S ≤ C) : S ≤ C.lineal := by
  simp [lineal] -- [sSup_coe]
  sorry

@[simp]
lemma lineal_submodule (S : Submodule R M) : (S : PointedCone R M).lineal = S := by
  sorry

@[simp] lemma lineal_top : (⊤ : PointedCone R M).lineal = ⊤ := lineal_submodule ⊤
@[simp] lemma lineal_bot : (⊥ : PointedCone R M).lineal = ⊥ := lineal_submodule ⊥

lemma span_inter_lineal_eq_lineal {C : PointedCone R M} {s : Set M} (h : span R s = C) :
    span R (s ∩ C.lineal) = C.lineal := by
  rw [← antisymm_iff (r := LE.le)]
  constructor
  · rw [← Submodule.span_eq (C.lineal : PointedCone R M)]
    exact Submodule.span_mono (by simp)
  · rw [← SetLike.coe_subset_coe]
    rw [Set.subset_def]
    intro x hx
    let S:= s ∩ C.lineal
    let S' := s \ C.lineal
    have hS : S ∪ S' = s := by simp [S, S']
    have hS' : S ∩ S' = ∅ := by aesop

    --have hs : s = (s ∩ C.lineal) ∪ ()
    -- rw [Submodule.mem_span_finite_of_mem_span] at h
    sorry

section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

-- @[simp] -- no simp because right side has twice as many `x`?
lemma lineal_mem {x : M} {C : PointedCone R M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  constructor
  · intro h
    have h' := neg_mem_iff.mpr h
    exact ⟨lineal_le C h, lineal_le C h'⟩
  · intro ⟨h, h'⟩
    let S := Submodule.span R {x, -x}
    have hSC : S ≤ C := by sorry
    have hSC := le_lineal hSC
    have hxS : x ∈ S := Submodule.mem_span_of_mem (by simp)
    exact hSC hxS -- maybe we could use the lemma that s ∪ -s spans a linear space (see above)

def lineal_inf_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by
  ext x; simp [lineal_mem]

def lineal_mem_neg (C : PointedCone R M) : C.lineal = {x ∈ C | -x ∈ C} := by
  ext x; simp; exact lineal_mem

@[simp]
lemma lineal_inf (C D : PointedCone R M) : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by
  ext x; simp [lineal_mem]; aesop

lemma neg_mem_of_mem_lineal {C : PointedCone R M} {x : M} (hx : x ∈ C.lineal) : -x ∈ C := by
  rw [← Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma mem_of_neg_mem_lineal {C : PointedCone R M} {x : M} (hx : -x ∈ C.lineal) : x ∈ C := by
  rw [Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

end Ring

end Ring_AddCommGroup


section Ring_LinearOrder

-- we have LinearOrder because then Module.Finite { c // 0 ≤ c } R
variable {R M : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

lemma ofSubmodule_fg_of_fg {S : Submodule R M} (hS : S.FG) : (S : PointedCone R M).FG
    := Submodule.restrictedScalars_fg_of_fg _ hS

/- We current struggle to implement the converse, see `fg_of_restrictedScalars_fg`. -/
alias coe_fg := ofSubmodule_fg_of_fg

@[simp]
lemma coe_fg_iff {S : Submodule R M} : (S : PointedCone R M).FG ↔ S.FG :=
  ⟨Submodule.fg_of_restrictedScalars_fg, coe_fg⟩

lemma span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span R (M := M) C).FG :=
  Submodule.span_scalars_FG R hC

lemma fg_top [Module.Finite R M] : (⊤ : PointedCone R M).FG :=
  ofSubmodule_fg_of_fg Module.Finite.fg_top

end Ring_LinearOrder

section Ring_AddCommGroup

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- ## Salient

/-- A salient cone has trivial lineality space, see `salient_iff_lineal_bot`. -/
abbrev Salient (C : PointedCone R M) := C.toConvexCone.Salient

lemma salient_iff_mem_neg {C : PointedCone R M} : C.Salient ↔ ∀ x ∈ C, x ≠ 0 → -x ∉ C := by rfl

lemma Salient.mem_neg_mem_zero {C : PointedCone R M} (hC : C.Salient)
    {x : M} (hx : x ∈ C) (hx' : -x ∈ C) : x = 0 := by
  specialize hC x hx
  rw [not_imp_not] at hC
  exact hC hx'

lemma salient_iff_lineal_bot {C : PointedCone R M} : C.Salient ↔ C.lineal = ⊥ := by
  constructor
  · intro h
    ext x
    simp only [lineal_mem, Submodule.mem_bot]
    exact ⟨fun H => h.mem_neg_mem_zero H.1 H.2, by simp +contextual⟩
  · intro h x hx
    rw [not_imp_not]
    intro hnx
    have hlin := lineal_mem.mpr ⟨hx, hnx⟩
    rw [h] at hlin
    exact hlin

lemma inf_salient {C : PointedCone R M} {S : Submodule R M} (hCS : Disjoint C.lineal S) :
    (C ⊓ S).Salient := by
  simp only [salient_iff_lineal_bot, lineal_inf, lineal_submodule, ← disjoint_iff, hCS]

lemma inf_sup_lineal {C : PointedCone R M} {S : Submodule R M} (hCS : Codisjoint C.lineal S) :
    (C ⊓ S) ⊔ C.lineal = C := by
  rw [le_antisymm_iff]
  constructor
  · exact sup_le_iff.mpr ⟨inf_le_left, lineal_le C⟩
  · intro x hx
    rw [Submodule.codisjoint_iff_exists_add_eq] at hCS
    obtain ⟨y, z, hy, hz, hyz⟩ := hCS x
    rw [Submodule.mem_sup]
    have hzC : z ∈ C := by
      have h := Submodule.add_mem C hx (neg_mem_of_mem_lineal hy)
      rw [← hyz, add_neg_cancel_comm] at h
      exact h
    exact ⟨z, by simp; exact ⟨hzC, hz⟩, y, hy, by rw [add_comm]; exact hyz⟩

section DivisionRing

variable {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma exists_salient_disj_sup_lineal (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient
      ∧ Disjoint C.lineal (Submodule.span R D)
      ∧ D ⊔ C.lineal = C := by
  have ⟨S, hDis, hCod⟩ := exists_isCompl C.lineal
  refine ⟨C ⊓ S, inf_salient hDis, Disjoint.mono_right ?_ hDis, inf_sup_lineal hCod⟩
  rw [← Submodule.span_eq (p := S)]
  exact Submodule.span_mono (by simp)

lemma exists_salient_submodul_disj_sup (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧
      ∃ S : Submodule R M, Disjoint S (Submodule.span R D) ∧ D ⊔ S = C := by
  obtain ⟨D, hSal, hDis, hSup⟩ := exists_salient_disj_sup_lineal C
  exact ⟨D, hSal, C.lineal, hDis, hSup⟩

end DivisionRing

lemma span_diff_lineal_pointy {C : PointedCone R M} {s : Set M} (h : span R s = C) :
    (span R (s \ C.lineal)).Salient := by
  sorry

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧ D ⊔ C.lineal = C := by
  have hT : ∃ T : Submodule R M, IsCompl C.lineal T := sorry
    -- Submodule.exists_isCompl (K := R) (V := M) C.lineal
  obtain ⟨CoLin, h⟩ := hT
  use (C ⊓ CoLin)
  constructor
  · sorry
  · sorry

/-- A cone is a sum of a pointed cone and its lineality space. -/
-- NOTE: I just realzed that this is true in a boring sense: let D := span C \ C.lineal ∪ {0}
lemma exists_pointy_sup_lineal' (C : PointedCone R M) :
    ∃ D : PointedCone R M, (Submodule.span R D) ⊓ C.lineal = ⊥ ∧ D ⊔ C.lineal = C := by

  sorry

/-- This is a variant of `IsModularLattice.sup_inf_assoc_of_le`. While submodules form a modular
  lattice, pointed cones do in general not. -/
lemma sup_inf_assoc_of_le_submodule {C : PointedCone R M} (D : PointedCone R M)
    {M : Submodule R M} (hCE : C ≤ M) : C ⊔ (D ⊓ M) = (C ⊔ D) ⊓ M := by
  ext x
  simp [Submodule.mem_sup]
  constructor
  · intro h
    obtain ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩ := h
    exact ⟨⟨y, hy, z, hz, hyzx⟩, by
      rw [← hyzx]; exact Submodule.add_mem M (hCE hy) hz' ⟩
  · intro h
    obtain ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩ := h
    exact ⟨y, hy, z, ⟨hz, by
      rw [← add_left_cancel_iff (a := -y), neg_add_cancel_left] at hyzx
      rw [hyzx]
      specialize hCE hy
      rw [Submodule.restrictScalars_mem, ← Submodule.neg_mem_iff] at hCE
      exact Submodule.add_mem M hCE hx
    ⟩, hyzx⟩

end Ring_AddCommGroup

end PointedCone
