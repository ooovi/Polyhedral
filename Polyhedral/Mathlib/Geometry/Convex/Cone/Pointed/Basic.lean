
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

end Semiring


-- ## COE

section Semiring_AddCommGroup

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M)
    := Submodule.restrictScalars_inf

lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  Submodule.restrictScalars_sInf

lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

-- lemma iInf_coe' (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
--   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf]

lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M)
    := Submodule.restrictScalars_sup

lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  Submodule.restrictScalars_sSup

lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]


/-- The submodule span of a finitely generated pointed cone is finitely generated. -/
lemma submodule_span_fg {C : PointedCone R M} (hC : C.FG) : (Submodule.span (M := M) R C).FG := by
  obtain ⟨s, rfl⟩ := hC; use s; simp

lemma coe_sup_submodule_span {C D : PointedCone R M} :
    Submodule.span R ((C : Set M) ⊔ (D : Set M)) = Submodule.span R (C ⊔ D : PointedCone R M) := by
  simp only [Set.sup_eq_union]
  rw [← span_submodule_span]
  congr; simp only [Submodule.span_union']

lemma span_le_submodule_span_of_le {s t : Set M} (hst : s ⊆ t) : span R s ≤ Submodule.span R t
  := le_trans (Submodule.span_le_restrictScalars _ R s) (Submodule.span_mono hst)

lemma span_le_submodule_span (s : Set M) : span R s ≤ Submodule.span R s
  := span_le_submodule_span_of_le (subset_refl s)

lemma le_submodule_span_of_le {C D : PointedCone R M} (hCD : C ≤ D) :
    C ≤ Submodule.span R (D : Set M) := by
  nth_rw 1 [← Submodule.span_eq C]
  exact span_le_submodule_span_of_le hCD

lemma le_submodule_span_self (C : PointedCone R M) : C ≤ Submodule.span R (C : Set M)
  := le_submodule_span_of_le (le_refl C)

alias le_span := subset_span


lemma submodule_span_of_span {s : Set M} {S : Submodule R M} (hsS : span R s = S) :
    Submodule.span R s = S := by
  simpa using congrArg (Submodule.span R ∘ SetLike.coe) hsS

lemma span_eq_submodule_span {s : Set M} (h : ∃ S : Submodule R M, span R s = S) :
    span R s = Submodule.span R s := by
  obtain ⟨S, hS⟩ := h; rw [hS]
  simpa using (congrArg (Submodule.span R ∘ SetLike.coe) hS).symm


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
omit [LinearOrder R] [IsOrderedRing R] in
variable (R) in
@[simp] lemma submodule_span_pm_pair (x : M) :
    Submodule.span R {-x, x} = Submodule.span R {x} := by
  rw [← Set.union_singleton, Submodule.span_union]; simp

variable (R) in
lemma span_sign_pair_eq_submodule_span_singleton (x : M) :
    span R {-x, x} = Submodule.span R {x} := by
  simpa [← submodule_span_pm_pair] using span_pm_pair_eq_submodule_span R x

-- NOTE: if this is implemented, it is more general than what mathlib already provides
-- for converting submodules into pointed cones. Especially the proof that R≥0 is an FG
-- submodule of R should be easier with this.
lemma span_union_neg_eq_span_submodule (s : Set M) :
    span R (-s ∪ s) = Submodule.span R s := by
  rw [Submodule.span_eq_iSup_of_singleton_spans]
  have H : ⨆ x ∈ s, Submodule.span R {x} = ⨆ x ∈ s, (Submodule.span R {x} : PointedCone R M) := by
    sorry -- rw [map_iSup (ofSubmodule (R:=R) (M:=M))
      -- (fun x => Submodule.span R (M:=M) {x}) (β := PointedCone R M)]
  rw [H]
  simp only [← span_sign_pair_eq_submodule_span_singleton]
  have H : ⨆ x ∈ s, span R {-x, x} = span R (⨆ x ∈ s, {-x, x}) := by
    sorry
  rw [H]
  congr; ext x
  simp only [Set.involutiveNeg, Set.mem_union, Set.mem_neg, Set.iSup_eq_iUnion, Set.mem_iUnion,
    Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop]
  constructor
  · intro h
    obtain (h | h) := h
    · exact ⟨-x, h, by simp⟩
    · exact ⟨x, h, by simp⟩
  · intro h
    obtain ⟨y, hy, hxy | hxy⟩ := h
    · rw [hxy]
      simp only [neg_neg]
      left; exact hy
    · rw [hxy]
      right; exact hy

  -- rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]
  -- ext x
  -- simp only [Set.involutiveNeg, Submodule.mem_span, Set.union_subset_iff, and_imp,
  --   Submodule.restrictScalars_mem]
  -- constructor
  -- · intro h S hsS
  --   specialize h S hsS
  --   nth_rw 1 [Submodule.coe_restrictScalars, Submodule.restrictScalars_mem,
  --     ← Submodule.neg_eq_self S, Submodule.coe_set_neg, Set.neg_subset_neg] at h
  --   exact h hsS
  -- · intro h C hsC hnsC
  --   have hh := subset_trans hsC (Submodule.subset_span (R := R))
  --   specialize h (Submodule.span R C) hh
  --   sorry

-- lemma span_union_neg_eq_span_submodule' (s : Set M) :
--     span R (s ∪ -s) = Submodule.span R s := by classical
--   rw [le_antisymm_iff]
--   constructor
--   · have h : Submodule.span R s = ↑(Submodule.span R (s ∪ -s)) := by
--       rw [Submodule.span_union]; simp
--     simpa [h] using span_le_submodule_span _
--   intro x hx
--   simp [Submodule.mem_span_iff_exists_finset_subset] at *
--   -- rw [Finsupp.mem_span_iff_linearCombination] at *
--   obtain ⟨f, t, hts, hft, hsum⟩ := hx
--   use fun x => ⟨if x ∈ t ∨ -x ∈ t then max 0 (f x) else 0, by sorry⟩
--   use t ∪ (Finset.image Neg.neg t)
--   simp
--   constructor
--   · constructor
--     · exact subset_trans hts (by simp)
--     · rw [← Set.neg_subset_neg]
--       simpa using subset_trans hts (by simp)
--   · constructor
--     · intro y hfy
--       sorry
--     · sorry

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

end Ring


section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M']

lemma map_span (f : M →ₗ[R] M') (s : Set M) : map f (span R s) = span R (f '' s) :=
  Submodule.map_span _ _

end Map

end Semiring_AddCommGroup


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

lemma neg_mem_of_mem_lineal {C : PointedCone R M} {x : M} (hx : x ∈ C.lineal) : -x ∈ C := by
  rw [← Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma mem_of_neg_mem_lineal {C : PointedCone R M} {x : M} (hx : -x ∈ C.lineal) : x ∈ C := by
  rw [Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- @[simp] -- no simp because right side has twice as many `x`?
lemma lineal_mem {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  constructor
  · intro h
    have h' := neg_mem_iff.mpr h
    exact ⟨lineal_le C h, lineal_le C h'⟩
  · intro ⟨h, h'⟩
    let S := Submodule.span R {-x, x}
    have hSC : S ≤ C := by
      have hx : ({-x, x} : Set M) ⊆ C := by
        intro x hx
        obtain (rfl | rfl) := hx
        exact h'; exact h
      have hx := Submodule.span_mono (R := {c : R // 0 ≤ c}) hx
      simp at hx
      simpa only [S, ← span_pm_pair_eq_submodule_span R] using hx
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

end Ring

section Semiring

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/- In this section we show properties of lineal that also follow from lineal
  being a face. But we need this earlier than faces, so we need to prove that
  lineal is a face here. This can then be resused later.

  Alternatively, lineal can be defined in Faces.lean
-/

lemma lineal_isExtreme_left {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal := by
  have hxy' := neg_mem_of_mem_lineal hxy
  have hx' := C.add_mem hy hxy'
  simp only [neg_add_rev, add_neg_cancel_left] at hx'
  exact lineal_mem.mpr ⟨hx, hx'⟩

lemma lineal_isExtreme_right {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : y ∈ C.lineal := by
  rw [add_comm] at hxy; exact lineal_isExtreme_left hy hx hxy

lemma lineal_isExtreme {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal ∧ y ∈ C.lineal :=
  ⟨lineal_isExtreme_left hx hy hxy, lineal_isExtreme_right hx hy hxy⟩

lemma lineal_isExtreme_right_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  have h := lineal_isExtreme_right hx (C.smul_mem (le_of_lt hc) hy) hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_left_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  have h := lineal_isExtreme_left (C.smul_mem (le_of_lt hc) hx) hy hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_sum {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (h : ∑ x ∈ xs, x ∈ C.lineal) : (xs : Set M) ⊆ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.sum_insert hy] at *
    have h := lineal_isExtreme hxs.1 (C.sum_mem hxs.2) h
    exact ⟨h.1, H hxs.2 h.2⟩

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma lineal_isExtreme_left' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  exact lineal_isExtreme_left_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_right' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  exact lineal_isExtreme_right_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_sum' {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (c : M → R) (hc : ∀ x ∈ xs, 0 < c x) (h : ∑ x ∈ xs, c x • x ∈ C.lineal) :
    ∀ x ∈ xs, c x ≠ 0 → x ∈ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, ne_eq, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.mem_insert, Finset.sum_insert hy] at *
    have hxsC := C.sum_mem (fun x hx => C.smul_mem (le_of_lt <| hc.2 x hx) (hxs.2 x hx))
    constructor
    · exact fun _ => lineal_isExtreme_left' hxs.1 hxsC hc.1 h
    · exact H hxs.2 hc.2 <| lineal_isExtreme_right (C.smul_mem (le_of_lt hc.1) hxs.1) hxsC h

variable (R) in
lemma span_inter_lineal_eq_lineal (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  rw [le_antisymm_iff]
  constructor
  · rw [← Submodule.span_eq <| ofSubmodule ((span R s).lineal)]
    refine Submodule.span_mono ?_
    simp only [Submodule.coe_restrictScalars, Set.inter_subset_right]
  · sorry
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

lemma FG.lineal_fg {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by classical
  obtain ⟨s, hs⟩ := hC
  use (s.finite_toSet.inter_of_left C.lineal).toFinset -- means {x ∈ s | x ∈ C.lineal}
  rw [submodule_span_of_span]
  simpa [← hs] using span_inter_lineal_eq_lineal R (s : Set M)

end DivisionRing

end Semiring

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

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

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

section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
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
