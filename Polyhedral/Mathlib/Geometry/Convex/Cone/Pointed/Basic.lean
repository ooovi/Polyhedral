
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

@[coe]
abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

instance : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

@[simp]
lemma ofSubmodule_coe (S : Submodule R M) : (ofSubmodule S : Set M) = S := by rfl
  -- also provable from `Submodule.coe_restrictScalars R S`

alias ofSubmodule_toSet_coe := ofSubmodule_coe

@[simp] lemma ofSubmodule_inj {S T : Submodule R M} : ofSubmodule S = ofSubmodule T ↔ S = T
  := Submodule.restrictScalars_inj ..

def ofSubmodule_embedding : Submodule R M ↪o PointedCone R M :=
  Submodule.restrictScalarsEmbedding ..

def ofSubmodule_latticeHom : CompleteLatticeHom (Submodule R M) (PointedCone R M) :=
  Submodule.restrictScalarsLatticeHom ..


-- ## SPAN

/- Intended new name for `PointedCone.span` to better avoid name clashes and confusion
  with `Submodule.span`. -/
alias hull := span

def span_gi : GaloisInsertion (span R : Set M → PointedCone R M) (↑) where
  choice s _ := span R s
  gc _ _ := Submodule.span_le
  le_l_u _ := subset_span
  choice_eq _ _ := rfl

@[simp] lemma span_submodule_span (s : Set M) :
    Submodule.span R (span R s) = Submodule.span R s := Submodule.span_span_of_tower ..

end Semiring

section Semiring_AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf

lemma sInf_coe (S : Set (Submodule R M)) : sInf S = sInf (ofSubmodule '' S) :=
  Submodule.restrictScalars_sInf

lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M)
    := Submodule.restrictScalars_sup

lemma sSup_coe (S : Set (Submodule R M)) : sSup S = sSup (ofSubmodule '' S) :=
  Submodule.restrictScalars_sSup

/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span (M := M) R C).FG := by
  obtain ⟨s, rfl⟩ := hC; use s; simp


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

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
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

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointed cones. Especially the proof that R≥0 is an FG
-- submodule of R should be easiert with this.
lemma span_union_neg_eq_span_submodule (s : Set M) :
    span R (s ∪ -s) = Submodule.span R s := by
  ext x
  simp only [Set.involutiveNeg, Submodule.mem_span, Set.union_subset_iff, and_imp,
    Submodule.restrictScalars_mem]
  constructor
  · intro h S hsS
    specialize h S hsS
    nth_rw 1 [Submodule.coe_restrictScalars, Submodule.restrictScalars_mem,
      ← Submodule.neg_eq_self S, Submodule.coe_set_neg, Set.neg_subset_neg] at h
    exact h hsS
  · intro h S hsS hnsS
    specialize h (Submodule.span R S)
    sorry

lemma sup_neg_eq_submodule_span (C : PointedCone R M) :
    C ⊔ -C = Submodule.span R (C : Set M) := by
  nth_rw 1 2 [← Submodule.span_eq C]
  rw [← Submodule.span_neg_eq_neg, ← Submodule.span_union]
  exact span_union_neg_eq_span_submodule (C : Set M)

lemma span_eq_submodule_span_of_neg_self {s : Set M} (hs : s = -s) :
    span R s = Submodule.span R s := by
  nth_rw 1 [← Set.union_self s]
  nth_rw 2 [hs]
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
  rw [← sup_neg_eq_submodule_span, sup_eq_left]
  exact neg_le_iff_neg_eq.symm

lemma neg_self_iff_eq_span_submodule' {C : PointedCone R M} :
    -C ≤ C ↔ Submodule.span R (C : Set M) = C
  := Iff.trans neg_le_iff_neg_eq neg_self_iff_eq_span_submodule

end Ring


section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_span (f : M →ₗ[R] M') (s : Set M) : map f (span R s) = span R (f '' s) :=
  Submodule.map_span _ _

end Map

end Semiring_AddCommGroup




section Ring

variable {R M : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid M] [Module R M]

lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ⊔ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  simp only [Set.sup_eq_union]
  rw [← span_submodule_span]
  congr; simp only [Submodule.span_union']

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

alias le_span := subset_span



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

lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp [lineal]

lemma le_lineal {C : PointedCone R M} {S : Submodule R M} (hS : S ≤ C) :
    S ≤ C.lineal := le_sSup hS

@[simp]
lemma lineal_submodule (S : Submodule R M) : (S : PointedCone R M).lineal = S := by
  rw [le_antisymm_iff]
  constructor
  · --apply ofSubmodule_embedding.strictMono
    --refine le_trans (lineal_le S) ?_
    --exact lineal_le S
    sorry
  · exact le_lineal (by simp)

@[simp] lemma lineal_top : (⊤ : PointedCone R M).lineal = ⊤ := lineal_submodule ⊤
@[simp] lemma lineal_bot : (⊥ : PointedCone R M).lineal = ⊥ := lineal_submodule ⊥

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

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

section DivisionRing

variable {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- In this section we show properties of lineal that also follow from lineal
  being a face. But we need this earlier than faces, so we need to prove that
  lineal is a face here. This can then be resused later.

  Alternatively, lineal can be defined in Faces.lean
-/

/- NOTE: move somewhere else -/
lemma submodule_span_of_span {s : Set M} {S : Submodule R M} (hsS : span R s = S) :
    Submodule.span R s = S := by
  simpa using congrArg (Submodule.span R ∘ SetLike.coe) hsS

/- NOTE: move somewhere else -/
lemma span_eq_submodule_span {s : Set M} (h : ∃ S : Submodule R M, span R s = S) :
    span R s = Submodule.span R s := by
  obtain ⟨S, hS⟩ := h; rw [hS]
  simpa using (congrArg (Submodule.span R ∘ SetLike.coe) hS).symm

lemma lineal_isExtreme {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : c > 0) (hxy : x + c • y ∈ C.lineal) : x ∈ C.lineal ∧ y ∈ C.lineal := by

  sorry

variable (R) in
lemma span_inter_lineal_eq_lineal (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  rw [← antisymm_iff (r := LE.le)]
  -- constructor
  -- · rw [← Submodule.span_eq (C.lineal : PointedCone R M)]
  --   exact Submodule.span_mono (by simp)
  -- · rw [← SetLike.coe_subset_coe]
  --   rw [Set.subset_def]
  --   intro x hx
  --   let S:= s ∩ C.lineal
  --   let S' := s \ C.lineal
  --   have hS : S ∪ S' = s := by simp [S, S']
  --   have hS' : S ∩ S' = ∅ := by aesop

  --   --have hs : s = (s ∩ C.lineal) ∪ ()
  --   -- rw [Submodule.mem_span_finite_of_mem_span] at h
    -- sorry
  sorry

lemma FG.lineal_fg {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by classical
  obtain ⟨s, hs⟩ := hC
  use (s.finite_toSet.inter_of_left C.lineal).toFinset -- means {x ∈ s | x ∈ C.lineal}
  rw [submodule_span_of_span]
  simpa [← hs] using span_inter_lineal_eq_lineal R (s : Set M)

end DivisionRing

end Ring_AddCommGroup


section Ring_LinearOrder

-- we have LinearOrder because then Module.Finite { c // 0 ≤ c } R
variable {R M : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid M]
  [Module R M]

lemma ofSubmodule_fg_of_fg {S : Submodule R M} (hS : S.FG) : (S : PointedCone R M).FG
    := Submodule.restrictedScalars_fg_of_fg _ hS

/- We current struggle to implement the converse, see `fg_of_restrictedScalars_fg`. -/
alias coe_fg := ofSubmodule_fg_of_fg

-- Q: is this problematic?
instance {S : Submodule R M} : Coe S.FG (S : PointedCone R M).FG := ⟨coe_fg⟩

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

/-- A pointed cone can be written as a sup of its lineality space and a complementary
  salient cone. -/
lemma exists_salient_disj_sup_lineal (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient
      ∧ Disjoint C.lineal (.span R D)
      ∧ D ⊔ C.lineal = C := by
  have ⟨S, hDis, hCod⟩ := exists_isCompl C.lineal
  refine ⟨C ⊓ S, inf_salient hDis, Disjoint.mono_right ?_ hDis, inf_sup_lineal hCod⟩
  rw [← Submodule.span_eq (p := S)]
  exact Submodule.span_mono (by simp)

/-- A pointed cone can be written as a sup of a submodule and a complementary
  salient cone. -/
lemma exists_salient_submodul_disj_sup (C : PointedCone R M) :
    ∃ D : PointedCone R M, D.Salient ∧
      ∃ S : Submodule R M, Disjoint S (.span R D) ∧ D ⊔ S = C := by
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
    {S : Submodule R M} (hCS : C ≤ S) : C ⊔ (D ⊓ S) = (C ⊔ D) ⊓ S := by
  ext x
  simp [Submodule.mem_sup]
  constructor
  · intro h
    obtain ⟨y, hy, z, ⟨hz, hz'⟩, hyzx⟩ := h
    exact ⟨⟨y, hy, z, hz, hyzx⟩, by
      rw [← hyzx]; exact S.add_mem (hCS hy) hz' ⟩
  · intro h
    obtain ⟨⟨y, hy, z, hz, hyzx⟩, hx⟩ := h
    exact ⟨y, hy, z, ⟨hz, by
      rw [← add_left_cancel_iff (a := -y), neg_add_cancel_left] at hyzx
      rw [hyzx]
      specialize hCS hy
      rw [Submodule.restrictScalars_mem, ← neg_mem_iff] at hCS
      exact S.add_mem hCS hx
    ⟩, hyzx⟩

end Ring_AddCommGroup

end PointedCone
