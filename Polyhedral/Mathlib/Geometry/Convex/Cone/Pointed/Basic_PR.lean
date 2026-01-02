
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Geometry.Convex.Cone.Pointed

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic_PR

namespace PointedCone

variable {R M : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]
variable {s : Set M}

-- Useful fopr pretty printing
@[coe]
abbrev ofSubmodule (S : Submodule R M) : PointedCone R M := S.restrictScalars _

-- priority high to dominate over pure restrictSclars
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

end AddCommMonoid

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

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simp]
lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

end Ring

end PointedCone
