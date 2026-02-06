
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Geometry.Convex.Cone.Pointed
import Polyhedral.PR.RestrictScalars_PR

open Function Submodule

namespace PointedCone

variable {R M : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]
variable {s : Set M}

@[coe]
abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

instance : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

-- priority high to dominate over pure restrictScalars
instance (priority := high) : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

@[simp]
lemma coe_ofSubmodule (S : Submodule R M) : (ofSubmodule S : Set M) = S := by rfl

@[simp]
lemma mem_ofSubmodule {S : Submodule R M} {x : M} : x ∈ (S : PointedCone R M) ↔ x ∈ S := by rfl

alias mem_coe := mem_ofSubmodule

@[simp] lemma ofSubmodule_inj {S T : Submodule R M} : ofSubmodule S = ofSubmodule T ↔ S = T
  := Submodule.restrictScalars_inj ..

def ofSubmodule_embedding : Submodule R M ↪o PointedCone R M :=
  Submodule.restrictScalarsEmbedding ..

def ofSubmodule_latticeHom : CompleteLatticeHom (Submodule R M) (PointedCone R M) :=
  Submodule.restrictScalarsLatticeHom ..

-- lemma ofSubmodule_sInf (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
--   ofSubmodule_latticeHom.map_sInf' s

-- lemma ofSubmodule_sSup (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
--   ofSubmodule_latticeHom.map_sSup' s

lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M) :=
  Submodule.restrictScalars_inf _

lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
  Submodule.restrictScalars_sInf _

lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
  rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

-- lemma iInf_coe' (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
--   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf]

lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M) :=
  Submodule.restrictScalars_sup _

lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
  Submodule.restrictScalars_sSup _

lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
  rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]

-- end AddCommMonoid

section AddCommGroup

-- ### NEG

variable [AddCommGroup M] [Module R M]

instance : InvolutiveNeg (PointedCone R M) := Submodule.involutivePointwiseNeg

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

section Map

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

end Map

end AddCommGroup

end Semiring


section Lineal

open Pointwise

variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]

/-- The lineality space of a cone `C` is the submodule given by `C ⊓ -C`. -/
def lineal (C : PointedCone R M) : Submodule R M where
  carrier := C ⊓ -C
  add_mem' hx hy := by simpa using ⟨C.add_mem hx.1 hy.1, C.add_mem hy.2 hx.2⟩
  zero_mem' := by simp
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

@[simp]
lemma lineal_eq_inf_neg (C : PointedCone R M) : C.lineal = C ⊓ -C :=
  rfl

lemma mem_lineal {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  rfl

@[simp]
lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp

/- The lineality space of a cone is the largest submodule contained in the cone. -/
theorem lineal_eq_sSup (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C} := by
  rw [le_antisymm_iff]
  refine ⟨le_sSup (lineal_le C), ?_⟩
  intro x hx
  have hC : sSup {S : Submodule R M | S ≤ C} ≤ C := by simp
  exact mem_lineal.mpr ⟨hC hx, hC (neg_mem hx : -x ∈ _)⟩

end Lineal

end PointedCone


-- import Mathlib.Algebra.Module.Submodule.Pointwise
-- import Mathlib.Geometry.Convex.Cone.Pointed

-- import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic_PR

-- namespace PointedCone

-- variable {R M : Type*}

-- section Semiring

-- variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

-- section AddCommMonoid

-- variable [AddCommMonoid M] [Module R M]
-- variable {s : Set M}

-- -- Useful fopr pretty printing
-- @[coe]
-- abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

-- -- priority high to dominate over pure restrictSclars
-- instance (priority := high) : Coe (Submodule R M) (PointedCone R M) := ⟨ofSubmodule⟩

-- @[simp]
-- lemma coe_ofSubmodule (S : Submodule R M) : (ofSubmodule S : Set M) = S := by rfl

-- @[simp]
-- lemma mem_ofSubmodule {S : Submodule R M} {x : M} : x ∈ (S : PointedCone R M) ↔ x ∈ S := by rfl

-- alias mem_coe := mem_ofSubmodule

-- @[simp] lemma ofSubmodule_inj {S T : Submodule R M} : ofSubmodule S = ofSubmodule T ↔ S = T
--   := Submodule.restrictScalars_inj ..

-- def ofSubmodule_embedding : Submodule R M ↪o PointedCone R M :=
--   Submodule.restrictScalarsEmbedding ..

-- def ofSubmodule_latticeHom : CompleteLatticeHom (Submodule R M) (PointedCone R M) :=
--   Submodule.restrictScalarsLatticeHom ..

-- -- lemma ofSubmodule_sInf (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
-- --   ofSubmodule_latticeHom.map_sInf' s

-- -- lemma ofSubmodule_sSup (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
-- --   ofSubmodule_latticeHom.map_sSup' s

-- lemma coe_inf (S T : Submodule R M) : S ⊓ T = (S ⊓ T : PointedCone R M) :=
--   Submodule.restrictScalars_inf _

-- lemma sInf_coe (s : Set (Submodule R M)) : sInf s = sInf (ofSubmodule '' s) :=
--   Submodule.restrictScalars_sInf _

-- lemma iInf_coe (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
--   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf, iInf_image]

-- -- lemma iInf_coe' (s : Set (Submodule R M)) : ⨅ S ∈ s, S = ⨅ S ∈ s, (S : PointedCone R M) := by
-- --   rw [← sInf_eq_iInf, sInf_coe, sInf_eq_iInf]

-- lemma coe_sup (S T : Submodule R M) : S ⊔ T = (S ⊔ T : PointedCone R M) :=
--   Submodule.restrictScalars_sup _

-- lemma sSup_coe (s : Set (Submodule R M)) : sSup s = sSup (ofSubmodule '' s) :=
--   Submodule.restrictScalars_sSup _

-- lemma iSup_coe (s : Set (Submodule R M)) : ⨆ S ∈ s, S = ⨆ S ∈ s, (S : PointedCone R M) := by
--   rw [← sSup_eq_iSup, sSup_coe, sSup_eq_iSup, iSup_image]

-- end AddCommMonoid

-- section AddCommGroup

-- -- ### NEG

-- variable [AddCommGroup M] [Module R M]

-- instance : InvolutiveNeg (PointedCone R M) := Submodule.involutivePointwiseNeg

-- -- TODO: Does this not already exist?
-- lemma map_id_eq_neg (C : PointedCone R M) : C.map (-.id) = -C := by
--   ext x
--   simp only [Submodule.mem_neg, mem_map, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
--   constructor
--   · intro h
--     obtain ⟨y, hyC, rfl⟩ := h
--     simpa using hyC
--   · exact fun h => by use -x; simp [h]

-- lemma comap_id_eq_neg (C : PointedCone R M) : C.comap (-.id) = -C := by
--   ext x; simp

-- section Map

-- variable {N : Type*} [AddCommGroup N] [Module R N]

-- lemma map_neg (C : PointedCone R M) (f : M →ₗ[R] N) : map (-f) C = map f (-C) := by
--   ext x
--   simp only [mem_map, LinearMap.neg_apply, Submodule.mem_neg]
--   constructor <;> {
--     intro h
--     obtain ⟨x, hx⟩ := h
--     exact ⟨-x, by simpa using hx⟩
--   }

-- lemma map_neg_apply (C : PointedCone R M) (f : M →ₗ[R] N) : - map f C = map f (-C) := by
--   ext x
--   simp
--   constructor <;> {
--     intro h
--     obtain ⟨x, hx⟩ := h
--     exact ⟨-x, by simpa [neg_eq_iff_eq_neg] using hx⟩
--   }

-- lemma comap_neg (C : PointedCone R M) (f : N →ₗ[R] M) : comap (-f) C = comap f (-C) := by
--   ext x; simp

-- lemma comap_neg_apply (C : PointedCone R M) (f : N →ₗ[R] M) : -comap f C = comap f (-C) := by
--   ext x; simp

-- end Map

-- end AddCommGroup

-- end Semiring

-- section Ring

-- variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
-- variable {M : Type*} [AddCommGroup M] [Module R M]

-- @[simp]
-- lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

-- end Ring

-- end PointedCone
