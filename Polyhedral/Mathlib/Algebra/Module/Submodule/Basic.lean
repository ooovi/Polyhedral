import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Noetherian.Defs

namespace Submodule

section Semiring

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

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

/- I suggest the alternative naming `restrict` for `submoduleOf` for the following reason:
  we want to have the same functionality on `PointedCone`, but there the name `submoduleOf`
  makes no sense. Using a different name would be inconsistent.
  Not also that this cannot be an alias of `submoduleOf` because the argument are in the
  opposite order. This is in order to be consistent with `embed` for which the other order
  is not possible.
-/

/-- The restriction of `S ⊓ T` considered as a submodule of `S`. -/
abbrev restrict (S T : Submodule R M) : Submodule R S := T.submoduleOf S -- T.comap S.subtype

@[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := submoduleOf_self S

lemma restrict_mono (S : Submodule R M) {T₁ T₂ : Submodule R M} (hCD : T₁ ≤ T₂) :
    restrict S T₁ ≤ restrict S T₂ := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {T₁ T₂ : Submodule R M} :
    restrict S (T₁ ⊓ T₂) = (restrict S T₁) ⊓ (restrict S T₂)
  := by ext x; simp [restrict, submoduleOf]

/-- A submodule `T` of a submodule `S` of `M` intepreted as a submodule of `M`. -/
abbrev embed {S : Submodule R M} (T : Submodule R S) : Submodule R M := T.map S.subtype

@[simp] lemma embed_restrict (S T : Submodule R M) : embed (restrict S T) = S ⊓ T
  := map_comap_subtype _ _

-- @[simp] lemma restrict_embed {S : Submodule R M} (T : Submodule R S) : restrict S (embed T) = T
--   := sorry

lemma embed_inj {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : embed T₁ = embed T₂) :
    T₁ = T₂ := by sorry

-- lemma embed_mono {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : embed T₁ ≤ embed T₂) :
--     T₁ ≤ T₂ := sorry

def embed_orderEmbed (S : Submodule R M) : OrderEmbedding (Submodule R S) (Submodule R M) where
  toFun := embed
  inj' := @embed_inj _ _ _ _ _ S
  map_rel_iff' := by
    intro T U
    simp
    sorry

section RestrictedScalar

variable {S : Type*} [Semiring S] [Module S R] [Module S M] [IsScalarTower S R M]

open Function

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

section Ring

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

-- Q: Does this really need Ring?
@[simp] lemma restrict_embed {S : Submodule R M} (T : Submodule R S) : restrict S (embed T) = T
  := by simp [submoduleOf, comap_map_eq]

def embed_gi (S : Submodule R M) : GaloisCoinsertion (embed) (restrict S) where
  choice := fun T _ => restrict S T
  gc T U := by
    constructor
    · intro h
      sorry
    · intro h
      sorry
  u_l_le T := le_of_eq (restrict_embed T)
  choice_eq := by simp


end Ring

-- section Field

-- variable {M R : Type*} [Ring R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]

-- lemma fg_of_submodule_of_finite [Module.Finite R M] (S : Submodule R M) : S.FG := by
--   have h : Module.Finite R S := Module.Finite.of_submodule
--   exact Module.Finite.iff_fg.mp h

-- end Field

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
