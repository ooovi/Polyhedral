
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Geometry.Convex.Cone.Pointed

import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic_PR

namespace PointedCone

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
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

end Semiring


section Semiring

-- ### NEG

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

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

end Semiring

section Ring

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

@[simp]
lemma neg_coe (S : Submodule R M) : -(S : PointedCone R M) = S := by ext x; simp

-- M: Only include the below once we push `linSpan`?

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

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

variable (R) in
lemma span_sign_pair_eq_submodule_span_singleton (x : M) :
    span R {-x, x} = Submodule.span R {x} := by
  simpa [← Submodule.submodule_span_pm_pair] using span_pm_pair_eq_submodule_span R x

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
  simp [Submodule.mem_span]
  constructor <;> intros h B sB
  · refine h (Submodule.restrictScalars {c // 0 ≤ c} B) ?_ sB
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

end Ring

end PointedCone
