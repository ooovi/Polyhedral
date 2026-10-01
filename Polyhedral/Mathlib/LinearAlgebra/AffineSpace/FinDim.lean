/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.FiniteDimensional
public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Order.SuccPred.WithBot

/-!
# Finite-dimensional subsets of affine spaces

`Affine.FinDim R s` means that the affine span of a set `s` has finitely generated
direction. Over a division ring this is finite-dimensionality. The abbreviation is
definitionally `Module.Finite R (vectorSpan R s)`, so existing assumptions on the vector
span can be written `[Affine.FinDim R s]` without conversion instances.

This is a predicate, distinct from the numerical dimension `Affine.finrank R s` and
`(affineSpan R s).finDim`. The empty set satisfies the predicate and its affine span has
dimension `⊥`. Closure lemmas take explicit proofs and register no additional instances.

The API includes affine-span and image invariance, finite unions, descent to subsets over
a division ring, dimension comparisons, and finite independent spanning subsets with
cardinality `(affineSpan R s).finDim.succ`. The last formulation also covers the empty set
and is suited to homogenization and grading of polytope faces.
-/

@[expose] public section

namespace Affine

/-- A subset of an affine space is finite-dimensional when its vector span is a finite module.
The definition also applies over rings, where it expresses finite generation. -/
abbrev FinDim (R : Type*) {V A : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [AddTorsor V A] (s : Set A) : Prop :=
  Module.Finite R (vectorSpan R s)

section Ring

variable {R V A : Type*} [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V A]
variable {s t : Set A}

theorem finDim_iff_vectorSpan : FinDim R s ↔ Module.Finite R (vectorSpan R s) := Iff.rfl

@[simp]
theorem finDim_coe_iff (S : AffineSubspace R A) : FinDim R (S : Set A) ↔ S.FinDim :=
  Iff.rfl

/-- View a finite-dimensional affine subspace as a finite-dimensional subset. -/
theorem _root_.AffineSubspace.FinDim.coe {S : AffineSubspace R A} (hS : S.FinDim) :
    FinDim R (S : Set A) :=
  (finDim_coe_iff S).mpr hS

/-- Finite-dimensionality is exactly finite-dimensionality of the affine span. -/
theorem finDim_iff_affineSpan : FinDim R s ↔ (_root_.affineSpan R s).FinDim := by
  unfold FinDim AffineSubspace.FinDim
  rw [direction_affineSpan]

@[simp]
theorem finDim_affineSpan_iff : FinDim R (_root_.affineSpan R s : Set A) ↔ FinDim R s := by
  rw [finDim_coe_iff, ← finDim_iff_affineSpan]

theorem finDim_congr (h : _root_.affineSpan R s = _root_.affineSpan R t) :
    FinDim R s ↔ FinDim R t := by
  rw [finDim_iff_affineSpan, h, ← finDim_iff_affineSpan]

namespace FinDim

theorem affineSpan (hs : FinDim R s) : (_root_.affineSpan R s).FinDim :=
  finDim_iff_affineSpan.mp hs

theorem of_affineSpan_eq (hs : FinDim R s) (h : _root_.affineSpan R t = _root_.affineSpan R s) :
    FinDim R t :=
  (finDim_congr h).mpr hs

/-- Every finite set of points is finite-dimensional, over any ring. -/
theorem of_finite (hs : s.Finite) : FinDim R s := by
  unfold FinDim
  rw [vectorSpan_def]
  exact Module.Finite.span_of_finite R (hs.vsub hs)

theorem finset (S : Finset A) : FinDim R (S : Set A) := of_finite S.finite_toSet

@[simp]
theorem empty : FinDim R (∅ : Set A) := of_finite Set.finite_empty

@[simp]
theorem singleton (p : A) : FinDim R ({p} : Set A) := of_finite (Set.finite_singleton p)

theorem of_subsingleton (hs : s.Subsingleton) : FinDim R s := of_finite hs.finite

theorem range {ι : Sort*} [Finite ι] (p : ι → A) : FinDim R (Set.range p) :=
  of_finite (Set.finite_range p)

/-- A finite union of finite-dimensional sets is finite-dimensional. The joining direction
between two disjoint affine spans is included in the proof. -/
theorem union (hs : FinDim R s) (ht : FinDim R t) : FinDim R (s ∪ t) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simpa using ht
  rcases t.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simpa using hs
  have : Module.Finite R (_root_.affineSpan R s).direction := hs.affineSpan
  have : Module.Finite R (_root_.affineSpan R t).direction := ht.affineSpan
  unfold FinDim
  rw [← direction_affineSpan, AffineSubspace.span_union,
    AffineSubspace.direction_sup (mem_affineSpan R hp) (mem_affineSpan R hq)]
  infer_instance

theorem insert (hs : FinDim R s) (p : A) : FinDim R (insert p s) := by
  simpa only [Set.singleton_union] using (singleton p).union hs

theorem biUnion {ι : Type*} (I : Finset ι) (S : ι → Set A)
    (hS : ∀ i ∈ I, FinDim R (S i)) : FinDim R (⋃ i ∈ I, S i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hS i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj ↦ hS j (Finset.mem_insert_of_mem hj)))

theorem iUnion {ι : Sort*} [Finite ι] (S : ι → Set A) (hS : ∀ i, FinDim R (S i)) :
    FinDim R (⋃ i, S i) := by
  classical
  let := Fintype.ofFinite (PLift ι)
  simpa only [Finset.mem_univ, Set.iUnion_true, Set.iUnion_plift_down] using
    biUnion Finset.univ (fun i : PLift ι ↦ S i.down) (fun i _ ↦ hS i.down)

section Image

variable {W B : Type*} [AddCommGroup W] [Module R W] [AddTorsor W B]

theorem image (hs : FinDim R s) (f : A →ᵃ[R] B) : FinDim R (f '' s) := by
  let := hs
  unfold FinDim
  rw [← f.map_vectorSpan]
  infer_instance

theorem of_image {f : A →ᵃ[R] B} (hs : FinDim R (f '' s)) (hf : Function.Injective f) :
    FinDim R s := by
  have : Module.Finite R ((vectorSpan R s).map f.linear) := by
    rw [f.map_vectorSpan]
    exact hs
  exact Module.Finite.equiv
    (Submodule.equivMapOfInjective f.linear (f.linear_injective_iff.mpr hf) _).symm

end Image

end FinDim

section Image

variable {W B : Type*} [AddCommGroup W] [Module R W] [AddTorsor W B]

theorem finDim_image_iff {f : A →ᵃ[R] B} (hf : Function.Injective f) :
    FinDim R (f '' s) ↔ FinDim R s :=
  ⟨fun h ↦ h.of_image hf, fun h ↦ h.image f⟩

@[simp]
theorem finDim_image_equiv_iff (e : A ≃ᵃ[R] B) : FinDim R (e '' s) ↔ FinDim R s :=
  finDim_image_iff (f := e.toAffineMap) e.injective

end Image

end Ring

section DivisionRing

variable {K V A : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddTorsor V A]
variable {s t : Set A}

@[simp]
theorem finDim_univ_iff :
    FinDim K (Set.univ : Set A) ↔ AffineSpace.FiniteDimensional K A := by
  rw [finDim_iff_affineSpan, AffineSubspace.span_univ,
    AffineSubspace.finiteDimensional_top_iff]

@[simp]
theorem finDim_union_iff : FinDim K (s ∪ t) ↔ FinDim K s ∧ FinDim K t := by
  constructor
  · intro h
    let := h
    exact ⟨Submodule.finiteDimensional_of_le
      (vectorSpan_mono K (Set.subset_union_left : s ⊆ s ∪ t)),
      Submodule.finiteDimensional_of_le
      (vectorSpan_mono K (Set.subset_union_right : t ⊆ s ∪ t))⟩
  · exact fun ⟨hs, ht⟩ ↦ hs.union ht

theorem finDim_iff_dim_lt_aleph0 :
    FinDim K s ↔ (_root_.affineSpan K s).dim < (Cardinal.aleph0 : WithBot Cardinal) := by
  rw [finDim_iff_affineSpan]
  exact AffineSubspace.finiteDimensional_iff_dim_lt_aleph0

theorem finDim_iff_rank_lt_aleph0 : FinDim K s ↔ rank K s < Cardinal.aleph0 := by
  unfold FinDim rank
  rw [direction_affineSpan]
  exact Module.rank_lt_aleph0_iff.symm

theorem finDim_iff_exists_finite_affineSpan :
    FinDim K s ↔ ∃ t : Set A, t.Finite ∧ _root_.affineSpan K t = _root_.affineSpan K s := by
  rw [finDim_iff_affineSpan, AffineSubspace.finiteDimensional_iff_exists_finite_affineSpan]

theorem finDim_iff_exists_finset_affineSpan :
    FinDim K s ↔ ∃ t : Finset A, _root_.affineSpan K (t : Set A) = _root_.affineSpan K s := by
  rw [finDim_iff_affineSpan, AffineSubspace.finiteDimensional_iff_exists_finset_affineSpan]

namespace FinDim

/-- Finite-dimensionality descends to every subset over a division ring. -/
theorem mono (ht : FinDim K t) (h : s ⊆ t) : FinDim K s := by
  let := ht
  exact Submodule.finiteDimensional_of_le (vectorSpan_mono K h)

theorem of_finiteDimensional [AffineSpace.FiniteDimensional K A] (s : Set A) : FinDim K s :=
  inferInstanceAs (Module.Finite K (vectorSpan K s))

theorem inter_left (hs : FinDim K s) (t : Set A) : FinDim K (s ∩ t) :=
  hs.mono Set.inter_subset_left

theorem inter_right (ht : FinDim K t) (s : Set A) : FinDim K (s ∩ t) :=
  ht.mono Set.inter_subset_right

theorem diff (hs : FinDim K s) (t : Set A) : FinDim K (s \ t) := hs.mono Set.sdiff_subset

theorem finrank_mono (ht : FinDim K t) (h : s ⊆ t) : finrank K s ≤ finrank K t := by
  let := ht
  unfold finrank
  rw [direction_affineSpan, direction_affineSpan]
  exact Submodule.finrank_mono (vectorSpan_mono K h)

theorem finDim_mono (ht : FinDim K t) (h : s ⊆ t) :
    (_root_.affineSpan K s).finDim ≤ (_root_.affineSpan K t).finDim := by
  have := ht.affineSpan
  exact AffineSubspace.finDim_mono (affineSpan_mono K h)

theorem finrank_eq_rank (hs : FinDim K s) : (finrank K s : Cardinal) = rank K s := by
  have := hs.affineSpan
  exact Module.finrank_eq_rank' K (_root_.affineSpan K s).direction

/-- Equal dimensions and inclusion imply equality of the affine spans, not necessarily of
the original sets. -/
theorem affineSpan_eq_of_subset_of_finDim_eq (ht : FinDim K t) (h : s ⊆ t)
    (hd : (_root_.affineSpan K s).finDim = (_root_.affineSpan K t).finDim) :
    _root_.affineSpan K s = _root_.affineSpan K t :=
  AffineSubspace.eq_of_le_of_finDim_eq ht.affineSpan (affineSpan_mono K h) hd

end FinDim

end DivisionRing

end Affine

section AffineIndependent

variable {K V A : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddTorsor V A]
variable {s : Set A}

/-- An independent set in a finite-dimensional affine span is finite. -/
theorem AffineIndepOn.finite_of_finDim (hi : AffineIndepOn K id s)
    (hs : Affine.FinDim K s) : s.Finite := by
  have h : FiniteDimensional K (vectorSpan K (Set.range ((↑) : s → A))) := by
    rw [Subtype.range_coe]
    exact hs
  exact (finiteDimensional_iff_setFinite K hi).mp h

/-- An independent set has one more point than its affine dimension. Using `WithBot.succ`
also covers the empty set: the successor of its dimension `⊥` is zero. -/
theorem AffineIndepOn.ncard_eq_succ_finDim_affineSpan (hi : AffineIndepOn K id s)
    [hs : Affine.FinDim K s] : s.ncard = (_root_.affineSpan K s).finDim.succ := by
  have hfinite := hi.finite_of_finDim hs
  rcases s.eq_empty_or_nonempty with rfl | hnonempty
  · simp
  rw [AffineSubspace.finDim_eq_finrank
    (by simpa [← Set.nonempty_iff_ne_empty] using hnonempty), direction_affineSpan,
    WithBot.succ_natCast, hi.finrank_vectorSpan hfinite hnonempty]
  exact (Nat.sub_add_cancel (Nat.succ_le_of_lt ((Set.ncard_pos hfinite).mpr hnonempty))).symm

theorem AffineIndependent.ncard_eq_succ_finDim_affineSpan
    (hi : AffineIndependent K ((↑) : s → A)) [Affine.FinDim K s] :
    s.ncard = (_root_.affineSpan K s).finDim.succ :=
  (show AffineIndepOn K id s from hi).ncard_eq_succ_finDim_affineSpan

namespace Affine.FinDim

/-- A finite-dimensional set contains a finite independent subset spanning the same affine
subspace. Its cardinality is already expressed in terms of the original set's dimension. -/
theorem exists_affineIndependent (hs : Affine.FinDim K s) :
    ∃ t ⊆ s, t.Finite ∧ _root_.affineSpan K t = _root_.affineSpan K s ∧
      AffineIndependent K ((↑) : t → A) ∧ t.ncard = (_root_.affineSpan K s).finDim.succ := by
  obtain ⟨t, ht, hspan, hi⟩ := _root_.exists_affineIndependent K V s
  have htDim : Affine.FinDim K t := hs.of_affineSpan_eq hspan
  have hai : AffineIndepOn K id t := hi
  let := htDim
  refine ⟨t, ht, hai.finite_of_finDim htDim, hspan, hi, ?_⟩
  rw [← hspan]
  exact hai.ncard_eq_succ_finDim_affineSpan

theorem exists_affineIndepOn (hs : Affine.FinDim K s) :
    ∃ t ⊆ s, t.Finite ∧ _root_.affineSpan K t = _root_.affineSpan K s ∧
      AffineIndepOn K id t ∧ t.ncard = (_root_.affineSpan K s).finDim.succ :=
  hs.exists_affineIndependent

theorem exists_finset_subset_affineSpan (hs : Affine.FinDim K s) :
    ∃ t : Finset A, (t : Set A) ⊆ s ∧ _root_.affineSpan K (t : Set A) = _root_.affineSpan K s := by
  classical
  obtain ⟨t, ht, hfinite, hspan, -, -⟩ := hs.exists_affineIndependent
  exact ⟨hfinite.toFinset, by simpa using ht, by simpa using hspan⟩

end Affine.FinDim

end AffineIndependent
