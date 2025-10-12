import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice

namespace Submodule

section Semiring

variable {M S R : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module S R] [Module R M] [Module S M] [IsScalarTower S R M]

section RestrictedScalar

variable (S) in
lemma restrictedScalars_fg_of_fg [Module.Finite S R] {s : Submodule R M} (hfg : s.FG) :
    (s.restrictScalars S).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans R s

-- Q: True?
lemma restrictedScalars_fg_iff_fg [Module.Finite S R] {s : Submodule R M} :
    (s.restrictScalars S).FG ↔ s.FG := by
  sorry
  -- constructor
  -- · intro h
  --   obtain ⟨t, ht⟩ := h
  --   use t
  --   sorry
  -- · intro _;
  --   rw [← Module.Finite.iff_fg] at *
  --   exact Module.Finite.trans R s

-- Converse ?
lemma span_scalars_FG [Module.Finite S R] {s : Submodule S M} (hfg : s.FG) :
    (span R (M := M) s).FG := by
  obtain ⟨t, ht⟩ := hfg
  use t; rw [← ht, Submodule.span_span_of_tower]

@[simp]
lemma restrictScalars_inf {s t : Submodule R M} :
    (s ⊓ t).restrictScalars S = (s.restrictScalars S) ⊓ (t.restrictScalars S) := by
  ext x; simp

@[simp]
lemma restrictScalars_sup {s t : Submodule R M} :
    (s ⊔ t).restrictScalars S = (s.restrictScalars S) ⊔ (t.restrictScalars S):= by
  ext x; simp [mem_sup]

end RestrictedScalar

example (S S' : Set M) : span R (S ∪ S') = (span R S) ⊔ (span R S')
  := Submodule.span_union S S' -- should `Submodule.span_union` be a simp lemma? Yael says possibly
example (S S' : Submodule R M) : span R (S ⊔ S' : Submodule R M) = S ⊔ S'
  := by simp

@[simp] lemma span_union' (S S' : Submodule R M) : span R (S ∪ S') = S ⊔ S'
  := by rw [Submodule.span_union]; simp
@[simp] lemma span_inter (S S' : Submodule R M) : span R (S ∩ S') = S ⊓ S'
    := by rw [←coe_inf, span_eq]

-- Q: Do we maybe want notation for this? For example: `S ⊓ᵣ T`?
/-- The restriction of `S ⊓ T` considered as a submodule of `S`. -/
abbrev restrict (S T : Submodule R M) : Submodule R S := T.comap S.subtype
/-- A submodule `T` of a submodule `S` of `M` intepreted as a submodule of `M`. -/
abbrev embed (S : Submodule R M) (T : Submodule R S) : Submodule R M := T.map S.subtype

-- def restrict_set (S : Set M) (T : Submodule R M) : Set T := S.preimage T.subtype

-- Q: is this a good idea? It is not in mathlib for a reason.
instance {S : Submodule R M} : CoeOut (Submodule R S) (Submodule R M) := ⟨embed S⟩

-- @[simp] -- not neede because simp already solves this goal
lemma embed_restrict (S T : Submodule R M) : embed S (restrict S T) = S ⊓ T
  := map_comap_subtype _ _

section Ring

variable {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]

@[simp]
lemma restrict_embed (S : Submodule R M) (T : Submodule R S) : restrict S (embed S T) = T
  := by simp [comap_map_eq]

end Ring

end Semiring

section DivisionRing

open LinearMap

variable {M S R : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The projection with range and kernel swapped. -/
def IsProj.flip {S : Submodule R M} {p : M →ₗ[R] M} (hp : IsProj S p) : M →ₗ[R] M
  := .id - p -- IsCompl.projection hp.isCompl.symm

lemma IsCompl.projection_isProj {S T : Submodule R M} (hST : IsCompl S T) :
    IsProj S (IsCompl.projection hST) where
  map_mem := projection_apply_mem hST
  map_id x hx := projection_apply_left hST ⟨x, hx⟩

variable {M S R : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

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

section CommSemiring

open LinearMap

variable {M S R : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]

lemma IsCompl.dual {S T : Submodule R M} (hST : IsCompl S T) :
    IsCompl T.dualAnnihilator S.dualAnnihilator := by
  sorry

variable {M S R : Type*} [Field R] [AddCommGroup M] [Module R M]

lemma IsProj.dualMap_dual_Annihilator {S : Submodule R M} (p : M →ₗ[R] M) (hp : IsProj S p) :
    IsProj (ker p).dualAnnihilator p.dualMap where
  map_mem x := sorry
  map_id x hx := sorry

lemma IsCompl.projection_dual {S T : Submodule R M} (hST : IsCompl S T) :
    (projection hST).dualMap = projection (dual hST) := by
  sorry

-- lemma IsProj.dual {S : Submodule R M} {p : M →ₗ[R] M} (hp : LinearMap.IsProj S p) :
--     LinearMap.IsProj (p.ker.dualAnnihilator) p.dualMap := by sorry

end CommSemiring

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
