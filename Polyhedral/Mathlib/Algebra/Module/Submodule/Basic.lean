import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Noetherian.Defs

namespace Submodule

open Function

section Semiring

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]


-- ## SPAN

-- Is this the better name?
protected alias span_gi := Submodule.gi

-- Q: Why does the following not exist?
-- instance {S : Submodule R M} : CoeOut (Submodule R S) (Submodule R M) := ⟨embed S⟩

alias le_span := subset_span

-- Q: should `Submodule.span_union` be a simp lemma? Yael says possibly
example (S S' : Set M) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S'

@[simp] lemma span_union' (S S' : Submodule R M) : span R (S ∪ S') = S ⊔ S'
  := (Submodule.gi R M).l_sup_u S S'

-- span_sup'
example (S S' : Submodule R M) : span R (S ⊔ S' : Submodule R M) = S ⊔ S' := span_eq _

@[simp] lemma span_inter (S S' : Submodule R M) : span R (S ∩ S') = S ⊓ S'
    := (Submodule.gi R M).l_inf_u S S'

alias span_inf := span_inter

lemma span_sSup (s : Set (Submodule R M)) :
    span R (sSup (SetLike.coe '' s)) = sSup s := (Submodule.gi R M).l_sSup_u_image s

lemma span_sInf (s : Set (Submodule R M)) :
    span R (sInf (SetLike.coe '' s)) = sInf s := (Submodule.gi R M).l_sInf_u_image s

lemma span_biUnion (s : Set (Submodule R M)) :
    span R (⋃ S ∈ s, S) = sSup s := by simpa using span_sSup s

lemma span_biInter (s : Set (Submodule R M)) :
    span R (⋂ S ∈ s, S) = sInf s := by simpa using span_sInf s

alias span_iInter := span_biInter


-- ## RESTRICT / EMBED

/- I suggest the alternative naming `restrict` for `submoduleOf` for the following reason:
  we want to have the same functionality on `PointedCone`, but there the name `submoduleOf`
  makes no sense. Using the same name is preferred for consistency.
  Not also that this cannot be an alias of `submoduleOf` because the argument are in the
  opposite order. This is in order to be consistent with `embed` for which the other order
  is not possible. This also allows us to view `restrict S` as the restriction operator.
-/

/-- The restriction of `S ⊓ T` reinterpreted as a submodule of `S`. -/
abbrev restrict (S T : Submodule R M) : Submodule R S := T.submoduleOf S -- T.comap S.subtype

-- Q: Shoud have `restrict` as an order hom? If yes, use the code below.
def restrict' (S : Submodule R M) : Submodule R M →o Submodule R S where
  toFun := (submoduleOf · S)
  monotone' := fun _ _ h _ => (h ·)

@[simp] lemma restrict_top (S : Submodule R M) : restrict S ⊤ = ⊤ := by
  simp only [submoduleOf, comap_top]
@[simp] lemma restrict_bot (S : Submodule R M) : restrict S ⊥ = ⊥ := by
  simp only [submoduleOf, comap_bot, ker_subtype]

lemma mem_restrict {S : Submodule R M} {T : Submodule R M} {x : S} (h : x ∈ restrict S T) :
    (x : M) ∈ T := by simpa using h

lemma mem_restrict_iff {S : Submodule R M} {T : Submodule R M} {x : S} :
    x ∈ restrict S T ↔ (x : M) ∈ T := by simp [submoduleOf]

@[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := submoduleOf_self S

lemma restrict_mono (S : Submodule R M) {T₁ T₂ : Submodule R M} (hCD : T₁ ≤ T₂) :
    restrict S T₁ ≤ restrict S T₂ := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {T₁ T₂ : Submodule R M} :
    restrict S (T₁ ⊓ T₂) = (restrict S T₁) ⊓ (restrict S T₂)
  := by ext x; simp [restrict, submoduleOf]

/-- A submodule `T` of a submodule `S` of `M` reintepreted as a submodule of `M`. -/
abbrev embed {S : Submodule R M} (T : Submodule R S) : Submodule R M := T.map S.subtype

-- Q: Shoud have `embed` as an order embedding? If yes, use the code below.
def embed' {S : Submodule R M} : Submodule R S ↪o Submodule R M where
  toFun := map S.subtype
  inj' := map_injective_of_injective S.subtype_injective
  map_rel_iff' := ⟨fun h x => by simpa using @h x, Submodule.map_mono⟩

lemma mem_embed_iff {S : Submodule R M} {T : Submodule R S} (x : S) :
    (x : M) ∈ embed T ↔ x ∈ T := by simp

lemma mem_of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    x ∈ S := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨hxS, _⟩ := hx
  exact hxS

abbrev of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) : S :=
  ⟨x, mem_of_mem_embed hx⟩

lemma of_mem_embed_mem {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    of_mem_embed hx ∈ T := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨_, h⟩ := hx
  exact h

@[simp] lemma embed_restrict (S T : Submodule R M) : embed (restrict S T) = S ⊓ T
  := map_comap_subtype _ _

@[simp] lemma restrict_embed {S : Submodule R M} (T : Submodule R S) : restrict S (embed T) = T
    := by ext x; simp [submoduleOf]

lemma embed_injective {S : Submodule R M} : Injective (embed (S := S))
  := map_injective_of_injective S.subtype_injective

@[simp] lemma embed_inj {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ = embed T₂ ↔ T₁ = T₂ := Injective.eq_iff embed_injective

lemma embed_mono {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : T₁ ≤ T₂) :
    embed T₁ ≤ embed T₂ := Submodule.map_mono hT

lemma embed_mono_rev {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : embed T₁ ≤ embed T₂) :
    T₁ ≤ T₂ := (by simpa using @hT ·)

@[simp] lemma embed_mono_iff {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ ≤ embed T₂ ↔ T₁ ≤ T₂ where
  mp := embed_mono_rev
  mpr := embed_mono

@[simp] lemma embed_top (S : Submodule R M) : embed (⊤ : Submodule R S) = S := by simp
@[simp] lemma embed_bot (S : Submodule R M) : embed (⊥ : Submodule R S) = ⊥ := map_bot _

lemma embed_le {S : Submodule R M} (T : Submodule R S) : embed T ≤ S := by
  simpa using embed_mono le_top

def embed_orderEmbed (S : Submodule R M) : Submodule R S ↪o Submodule R M where
  toFun := embed
  inj' := embed_injective
  map_rel_iff' := embed_mono_iff

def embed_CompleteLatticeHom (S : Submodule R M) :
    CompleteLatticeHom (Submodule R S) (Submodule R M) where
  toFun := embed
  map_sInf' := by
    intro s
    unfold embed
    sorry
  map_sSup' := by
    intro s
    unfold embed
    sorry

def embed_gi (S : Submodule R M) : GaloisCoinsertion (embed) (restrict S) where
  choice := fun T _ => restrict S T
  gc T U := by
    simp [← embed_mono_iff, embed_restrict, le_inf_iff, iff_and_self]
    exact fun _ => embed_le T
  u_l_le T := le_of_eq (restrict_embed T)
  choice_eq := by simp


-- ## RESTRICT SCALARS

section RestrictedScalar

variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]

open Function

lemma restrictScalars_mono {s t : Submodule R M} (hST : s ≤ t) :
    s.restrictScalars S ≤ t.restrictScalars S := (restrictScalarsEmbedding S R M).monotone hST

@[simp] lemma restrictScalars_inf {s t : Submodule R M} :
    (s ⊓ t).restrictScalars S = (s.restrictScalars S) ⊓ (t.restrictScalars S) := by
  ext x; simp

@[simp] lemma restrictScalars_sup {s t : Submodule R M} :
    (s ⊔ t).restrictScalars S = (s.restrictScalars S) ⊔ (t.restrictScalars S):= by
  ext x; simp [mem_sup]

@[simp] lemma restrictScalars_sSup {s : Set (Submodule R M)} :
    (sSup s).restrictScalars S = sSup (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sSup' s

@[simp] lemma restrictScalars_sInf {s : Set (Submodule R M)} :
    (sInf s).restrictScalars S = sInf (restrictScalars S '' s) :=
  (restrictScalarsLatticeHom S R M).map_sInf' s

end RestrictedScalar

end Semiring

section DivisionRing

open LinearMap

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

-- /-- The projection with range and kernel swapped. -/
-- def IsProj.flip {S : Submodule R M} {p : M →ₗ[R] M} (hp : IsProj S p) : M →ₗ[R] M
--   := .id - p -- IsCompl.projection hp.isCompl.symm

lemma IsCompl.projection_isProj {S T : Submodule R M} (hST : IsCompl S T) :
    IsProj S (IsCompl.projection hST) where
  map_mem := projection_apply_mem hST
  map_id x hx := projection_apply_left hST ⟨x, hx⟩

variable {M R : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

lemma exists_isProj (S : Submodule R M) : ∃ p : M →ₗ[R] M, IsProj S p := by
  have ⟨_, hS'⟩ := exists_isCompl S
  exact ⟨_, IsCompl.projection_isProj hS'⟩

lemma exists_extend {T S : Submodule R M} (hST : S ≤ T) :
    ∃ S' : Submodule R M, S' ⊔ T = ⊤ ∧ S' ⊓ T = S := by
  have ⟨T', ⟨hdis, hcod⟩⟩ := exists_isCompl T
  use T' ⊔ S
  rw [codisjoint_iff] at hcod
  rw [disjoint_iff] at hdis
  rw [sup_comm, ← sup_assoc, hcod, inf_comm, ← inf_sup_assoc_of_le, hdis]
  · simp
  · exact hST

-- lemma exists_extend' (T : Submodule R M) (S : Submodule R T) :
--     ∃ S' : Submodule R M, S' ⊔ T = ⊤ ∧ S'.restrict T = S := by
--   use exists_extend (T:=T) (S:=(S : Submodule R M)) (by sorry)
--   sorry

end DivisionRing

section Ring

variable {M S R : Type*} [Ring R] [Ring S]
  [AddCommGroup M] [Module S R] [Module R M] [Module S M] [IsScalarTower S R M]

lemma IsCompl.foo (S₁ S₂ T : Submodule R M) (hS : IsCompl S₁ S₂) :
    IsCompl (T.restrict S₁) (T.restrict S₂) := by
  constructor
  · intro Q hQQ hQT
    sorry
  · sorry

lemma IsCompl.foo' (A B C D : Submodule R M) (hAB : Disjoint A B) (hCD : Disjoint C D)
    (h : IsCompl (A ⊔ B) (C ⊔ D)) : IsCompl (A ⊔ C) (B ⊔ D) := by
  sorry

lemma IsCompl.inf_sup (S₁ S₂ T₁ T₂ : Submodule R M) (hS : IsCompl S₁ S₂) (hT : IsCompl T₁ T₂) :
    IsCompl (T₁ ⊓ S₁) (S₂ ⊔ T₂) := by
  sorry
  -- ## Proof via projections
  -- let projS := Submodule.IsCompl.projection hS
  -- let projT := Submodule.IsCompl.projection hT
  -- let proj := projS ∘ₗ projT
  -- --have hprojS := IsCompl.IsPorj
  -- have hST₂: LinearMap.ker proj = T₁ ⊓ S₁ :=
  --   sorry
  -- have hST₂: Set.range proj = S₂ ⊔ T₂ :=
  --   sorry
  -- -- apply LinearMap.IsProj.isCompl (f := proj)
  -- sorry

end Ring

end Submodule
