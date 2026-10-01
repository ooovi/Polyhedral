/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Finite-dimensional affine subspaces

`AffineSubspace.FinDim s` means that the direction of `s` is a finite module.
Over a division ring this is finite-dimensionality; over a general ring it is finite generation.
It abbreviates `Module.Finite`, as does `FiniteDimensional` for vector spaces.
The closure lemmas in this file take explicit proofs of this predicate and register no
additional instances. A proof can still be installed locally with `let := hs` to use
Mathlib's API for `s.direction`, `s.dim`, and `s.finDim`.

The empty subspace is finite-dimensional, although its affine dimension is `⊥`.
Infinite-dimensional subspaces have the junk value `finDim = 0`; use `dim < ℵ₀` to
characterize finite-dimensionality instead.

Finite-dimensionality of an affine space is expressed separately by
`AffineSpace.FiniteDimensional K P`. For a nonempty subspace `s`, the two notions agree when
`s` is viewed as an affine space modeled on `s.direction`.
-/

@[expose] public section

namespace AffineSubspace

variable {K V P : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- An affine subspace is finite-dimensional if its direction is a finite module.
In particular, the empty affine subspace is finite-dimensional. -/
abbrev FinDim {R V A : Type*} [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V A]
    (s : AffineSubspace R A) : Prop :=
  Module.Finite R s.direction

variable {s t : AffineSubspace K P}

theorem finDim_iff_direction :
    s.FinDim ↔ _root_.FiniteDimensional K s.direction := Iff.rfl

/-- A nonempty affine subspace has the same finite-dimensionality as its underlying affine
space. This comparison is a theorem, not an instance. -/
theorem finDim_iff_affineSpace (s : AffineSubspace K P) [Nonempty s] :
    s.FinDim ↔ AffineSpace.FiniteDimensional K s := Iff.rfl

theorem dim_eq_affine_dim (s : AffineSubspace K P) [Nonempty s] :
    s.dim = (AffineSpace.dim K s : WithBot Cardinal) :=
  dim_eq_rank (nonempty_iff_ne_bot s |>.mp (Set.nonempty_coe_sort.mp inferInstance))

theorem finDim_eq_affine_finDim (s : AffineSubspace K P) [Nonempty s] :
    s.finDim = (AffineSpace.finDim K s : WithBot ℕ) :=
  finDim_eq_finrank (nonempty_iff_ne_bot s |>.mp (Set.nonempty_coe_sort.mp inferInstance))

@[simp]
theorem finDim_top_iff :
    (⊤ : AffineSubspace K P).FinDim ↔ _root_.FiniteDimensional K V := by
  unfold FinDim
  rw [direction_top]
  exact ⟨fun h ↦ by
    let := h
    exact Submodule.topEquiv.finiteDimensional, fun h ↦ by
    let := h
    infer_instance⟩

@[simp]
theorem finDim_toAffineSubspace_iff (S : Submodule K V) :
    S.toAffineSubspace.FinDim ↔ _root_.FiniteDimensional K S := by
  unfold FinDim
  rw [Submodule.toAffineSubspace_direction]

theorem FinDim.toAffineSubspace (S : Submodule K V)
    (hS : _root_.FiniteDimensional K S) : S.toAffineSubspace.FinDim :=
  (finDim_toAffineSubspace_iff S).mpr hS

theorem FinDim.mk' (p : P) (S : Submodule K V)
    (hS : _root_.FiniteDimensional K S) : (mk' p S).FinDim := by
  unfold FinDim
  rw [direction_mk']
  exact hS

/-- Every affine subspace of a finite-dimensional ambient space is finite-dimensional. -/
theorem FinDim.of_finiteDimensional
    [AffineSpace.FiniteDimensional K P] (s : AffineSubspace K P) : s.FinDim :=
  inferInstanceAs (_root_.FiniteDimensional K s.direction)

theorem FinDim.bot : (⊥ : AffineSubspace K P).FinDim := by
  unfold FinDim
  rw [direction_bot]
  infer_instance

/-- Finite-dimensionality descends to affine subspaces. -/
theorem FinDim.mono (ht : t.FinDim) (h : s ≤ t) :
    s.FinDim := by
  let := ht
  exact Submodule.finiteDimensional_of_le (direction_le h)

theorem FinDim.inf_left (s t : AffineSubspace K P) (hs : s.FinDim) :
    (s ⊓ t).FinDim :=
  FinDim.mono hs inf_le_left

theorem FinDim.inf_right (s t : AffineSubspace K P) (ht : t.FinDim) :
    (s ⊓ t).FinDim :=
  FinDim.mono ht inf_le_right

/-- An indexed intersection is finite-dimensional if one of its members is. -/
theorem FinDim.iInf {ι : Sort*} (S : ι → AffineSubspace K P) (i : ι)
    (hi : (S i).FinDim) : (⨅ j, S j).FinDim :=
  FinDim.mono hi (iInf_le S i)

theorem FinDim.finset_sup {ι : Type*} (I : Finset ι)
    (S : ι → AffineSubspace K P) (hS : ∀ i ∈ I, (S i).FinDim) :
    (I.sup S).FinDim := by
  refine Finset.sup_induction FinDim.bot ?_ hS
  intro s hs t ht
  let := hs
  let := ht
  infer_instance

theorem FinDim.iSup {ι : Sort*} [Finite ι] (S : ι → AffineSubspace K P)
    (hS : ∀ i, (S i).FinDim) : (⨆ i, S i).FinDim := by
  classical
  let := Fintype.ofFinite (PLift ι)
  simpa only [Finset.sup_univ_eq_iSup, iSup_plift_down] using
    FinDim.finset_sup Finset.univ (fun i : PLift ι ↦ S i.down) (fun i _ ↦ hS i.down)

/-- A singleton is finite-dimensional, even in an infinite-dimensional ambient space. -/
theorem FinDim.singleton (p : P) : ({p} : AffineSubspace K P).FinDim :=
  inferInstance

/-- Binary joins preserve finite-dimensionality. -/
theorem FinDim.sup (hs : s.FinDim)
    (ht : t.FinDim) : (s ⊔ t).FinDim := by
  let := hs
  let := ht
  infer_instance

/-- The affine span of a finite set is finite-dimensional. -/
theorem FinDim.affineSpan_of_finite {S : Set P} (hS : S.Finite) :
    (affineSpan K S).FinDim :=
  finiteDimensional_direction_affineSpan_of_finite K hS

theorem FinDim.affineSpan_finset (S : Finset P) :
    (affineSpan K (S : Set P)).FinDim :=
  FinDim.affineSpan_of_finite S.finite_toSet

/-- The affine span of a subset of a finite-dimensional subspace is finite-dimensional. -/
theorem FinDim.affineSpan_of_subset (hs : s.FinDim) {S : Set P}
    (hS : S ⊆ s) : (affineSpan K S).FinDim :=
  FinDim.mono hs (affineSpan_le.mpr hS)

section Map

variable {W Q : Type*} [AddCommGroup W] [Module K W] [AddTorsor W Q]

theorem FinDim.map (hs : s.FinDim) (f : P →ᵃ[K] Q) :
    (s.map f).FinDim := by
  let := hs
  infer_instance

/-- Finite-dimensionality descends along an injective affine map. -/
theorem FinDim.of_map {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    (hs : (s.map f).FinDim) : s.FinDim := by
  have : _root_.FiniteDimensional K (s.direction.map f.linear) := by
    rw [← map_direction]
    exact hs
  exact (Submodule.equivMapOfInjective f.linear
    (f.linear_injective_iff.mpr hf) s.direction).symm.finiteDimensional

theorem finDim_map_iff {f : P →ᵃ[K] Q} (hf : Function.Injective f) :
    (s.map f).FinDim ↔ s.FinDim := by
  constructor
  · exact FinDim.of_map hf
  · exact fun h ↦ FinDim.map h f

/-- An injective affine preimage of a finite-dimensional subspace is finite-dimensional. -/
theorem FinDim.comap_of_injective {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    (t : AffineSubspace K Q) (ht : t.FinDim) : (t.comap f).FinDim :=
  FinDim.of_map hf (FinDim.mono ht (map_comap_le f t))

@[simp]
theorem finDim_map_equiv_iff (e : P ≃ᵃ[K] Q) :
    (s.map e.toAffineMap).FinDim ↔ s.FinDim :=
  finDim_map_iff e.injective

end Map

/-- Finite-dimensional affine subspaces are precisely the affine spans of finite sets. -/
theorem finDim_iff_exists_finite_affineSpan :
    s.FinDim ↔ ∃ S : Set P, S.Finite ∧ affineSpan K S = s := by
  constructor
  · intro hs
    let := hs
    obtain ⟨S, -, hS, hI⟩ := exists_affineIndependent K V (s : Set P)
    have hspan : affineSpan K S = s := hS.trans (affineSpan_coe s)
    have : (affineSpan K S).FinDim := hspan ▸ hs
    have : _root_.FiniteDimensional K (vectorSpan K (Set.range ((↑) : S → P))) := by
      rw [Subtype.range_coe, ← direction_affineSpan]
      exact (inferInstance : (affineSpan K S).FinDim)
    exact ⟨S, (finiteDimensional_iff_setFinite K hI).mp inferInstance, hspan⟩
  · rintro ⟨S, hS, rfl⟩
    exact FinDim.affineSpan_of_finite hS

theorem finDim_iff_exists_finset_affineSpan :
    s.FinDim ↔ ∃ S : Finset P, affineSpan K (S : Set P) = s := by
  classical
  rw [finDim_iff_exists_finite_affineSpan]
  exact ⟨fun ⟨S, hS, hspan⟩ ↦ ⟨hS.toFinset, by simpa using hspan⟩,
    fun ⟨S, hspan⟩ ↦ ⟨S, S.finite_toSet, hspan⟩⟩

/-- The cardinal-valued dimension detects finite-dimensionality, including for `⊥`. -/
theorem finDim_iff_dim_lt_aleph0 :
    s.FinDim ↔ s.dim < (Cardinal.aleph0 : WithBot Cardinal) :=
  finite_iff_dim_lt_aleph0 s

/-- In finite dimension, the cardinal dimension is the natural dimension cast to cardinals.
This formulation also applies to the empty subspace. -/
theorem dim_eq_map_finDim (hs : s.FinDim) :
    s.dim = s.finDim.map (fun n : ℕ ↦ (n : Cardinal)) := by
  let := hs
  rcases eq_or_ne s ⊥ with rfl | hbot
  · simp
  rw [dim_eq_rank hbot, finDim_eq_finrank hbot, WithBot.map_natCast, WithBot.coe_inj]
  exact (Module.finrank_eq_rank' (K := K) (V := s.direction)).symm

/-- A finite-dimensional affine subspace is determined by inclusion and finite dimension. -/
theorem eq_of_le_of_finDim_eq (ht : t.FinDim) (h : s ≤ t)
    (hd : s.finDim = t.finDim) : s = t := by
  let := ht
  by_contra hne
  exact (ne_of_lt (finDim_strictMono (lt_of_le_of_ne h hne))) hd

theorem finDim_eq_iff_eq_of_le (ht : t.FinDim) (h : s ≤ t) :
    s.finDim = t.finDim ↔ s = t :=
  ⟨eq_of_le_of_finDim_eq ht h, fun h ↦ congrArg finDim h⟩

theorem lt_iff_finDim_lt_of_le (ht : t.FinDim) (h : s ≤ t) :
    s < t ↔ s.finDim < t.finDim := by
  let := ht
  refine ⟨finDim_strictMono, fun hd ↦ lt_of_le_of_ne h ?_⟩
  intro heq
  exact (ne_of_lt hd) (congrArg finDim heq)

end AffineSubspace
