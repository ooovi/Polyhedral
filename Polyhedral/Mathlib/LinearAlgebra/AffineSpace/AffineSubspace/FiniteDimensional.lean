/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Dimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Finite-dimensional affine subspaces

`AffineSubspace.FiniteDimensional s` means that the direction of `s` is finite-dimensional.
It is an abbreviation, just as `FiniteDimensional` is an abbreviation for `Module.Finite`.
Thus `[s.FiniteDimensional]` works directly with the existing API for `s.direction`, `s.dim`,
and `s.finDim`, without conversion instances.

The empty subspace is finite-dimensional, although its affine dimension is `⊥`.
Infinite-dimensional subspaces have the junk value `finDim = 0`; use `dim < ℵ₀` to
characterize finite-dimensionality instead.

Mathlib already supplies instances for singletons, affine spans of finite families, binary
suprema, affine images, and adjoining a point. This file adds instances for subspaces of a
finite-dimensional ambient space, intersections, finite suprema, and affine spans of finsets.
It also provides descent along injective affine maps, finite generating sets, and dimension
criteria for equality and strict inclusion.
-/

@[expose] public section

namespace AffineSubspace

variable {K V P : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddTorsor V P]

/-- An affine subspace is finite-dimensional if its direction is finite-dimensional.
In particular, the empty affine subspace is finite-dimensional. -/
abbrev FiniteDimensional (s : AffineSubspace K P) : Prop :=
  _root_.FiniteDimensional K s.direction

variable {s t : AffineSubspace K P}

theorem finiteDimensional_iff_direction :
    s.FiniteDimensional ↔ _root_.FiniteDimensional K s.direction := Iff.rfl

@[simp]
theorem finiteDimensional_top_iff :
    (⊤ : AffineSubspace K P).FiniteDimensional ↔ _root_.FiniteDimensional K V := by
  unfold FiniteDimensional
  rw [direction_top]
  exact ⟨fun h ↦ by
    let := h
    exact Submodule.topEquiv.finiteDimensional, fun h ↦ by
    let := h
    infer_instance⟩

@[simp]
theorem finiteDimensional_toAffineSubspace_iff (S : Submodule K V) :
    S.toAffineSubspace.FiniteDimensional ↔ _root_.FiniteDimensional K S := by
  unfold FiniteDimensional
  rw [Submodule.toAffineSubspace_direction]

instance finiteDimensional_toAffineSubspace (S : Submodule K V)
    [_root_.FiniteDimensional K S] : S.toAffineSubspace.FiniteDimensional :=
  (finiteDimensional_toAffineSubspace_iff S).mpr inferInstance

instance finiteDimensional_mk' (p : P) (S : Submodule K V)
    [_root_.FiniteDimensional K S] : (mk' p S).FiniteDimensional := by
  unfold FiniteDimensional
  rw [direction_mk']
  infer_instance

/-- Every affine subspace of a finite-dimensional ambient space is finite-dimensional. -/
instance (priority := low) finiteDimensional_of_finiteDimensional
    [_root_.FiniteDimensional K V] (s : AffineSubspace K P) : s.FiniteDimensional :=
  inferInstanceAs (_root_.FiniteDimensional K s.direction)

instance finiteDimensional_bot : (⊥ : AffineSubspace K P).FiniteDimensional := by
  unfold FiniteDimensional
  rw [direction_bot]
  infer_instance

/-- Finite-dimensionality descends to affine subspaces. -/
theorem finiteDimensional_of_le [t.FiniteDimensional] (h : s ≤ t) : s.FiniteDimensional :=
  Submodule.finiteDimensional_of_le (direction_le h)

instance finiteDimensional_inf_left (s t : AffineSubspace K P) [s.FiniteDimensional] :
    (s ⊓ t).FiniteDimensional :=
  finiteDimensional_of_le inf_le_left

instance finiteDimensional_inf_right (s t : AffineSubspace K P) [t.FiniteDimensional] :
    (s ⊓ t).FiniteDimensional :=
  finiteDimensional_of_le inf_le_right

/-- An indexed intersection is finite-dimensional if one of its members is. -/
theorem finiteDimensional_iInf {ι : Sort*} (S : ι → AffineSubspace K P) (i : ι)
    [(S i).FiniteDimensional] : (⨅ j, S j).FiniteDimensional :=
  finiteDimensional_of_le (iInf_le S i)

instance finiteDimensional_finset_sup {ι : Type*} (I : Finset ι)
    (S : ι → AffineSubspace K P) [∀ i, (S i).FiniteDimensional] :
    (I.sup S).FiniteDimensional := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (inferInstance : (⊥ : AffineSubspace K P).FiniteDimensional)
  | @insert i I hi hI =>
    let := hI
    rw [Finset.sup_insert]
    infer_instance

instance finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι → AffineSubspace K P)
    [∀ i, (S i).FiniteDimensional] : (⨆ i, S i).FiniteDimensional := by
  classical
  let := Fintype.ofFinite (PLift ι)
  simpa only [Finset.sup_univ_eq_iSup, iSup_plift_down] using
    (inferInstance : (Finset.univ.sup (fun i : PLift ι ↦ S i.down)).FiniteDimensional)

/-- The affine span of a finite set is finite-dimensional. -/
theorem finiteDimensional_affineSpan_of_finite {S : Set P} (hS : S.Finite) :
    (affineSpan K S).FiniteDimensional :=
  finiteDimensional_direction_affineSpan_of_finite K hS

instance finiteDimensional_affineSpan_finset (S : Finset P) :
    (affineSpan K (S : Set P)).FiniteDimensional :=
  finiteDimensional_affineSpan_of_finite S.finite_toSet

/-- The affine span of a subset of a finite-dimensional subspace is finite-dimensional. -/
theorem finiteDimensional_affineSpan_of_subset [s.FiniteDimensional] {S : Set P}
    (hS : S ⊆ s) : (affineSpan K S).FiniteDimensional :=
  finiteDimensional_of_le (affineSpan_le.mpr hS)

section Map

variable {W Q : Type*} [AddCommGroup W] [Module K W] [AddTorsor W Q]

/-- Finite-dimensionality descends along an injective affine map. -/
theorem finiteDimensional_of_map {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    [(s.map f).FiniteDimensional] : s.FiniteDimensional := by
  have : _root_.FiniteDimensional K (s.direction.map f.linear) := by
    rw [← map_direction]
    exact (inferInstance : (s.map f).FiniteDimensional)
  exact (Submodule.equivMapOfInjective f.linear
    (f.linear_injective_iff.mpr hf) s.direction).symm.finiteDimensional

theorem finiteDimensional_map_iff {f : P →ᵃ[K] Q} (hf : Function.Injective f) :
    (s.map f).FiniteDimensional ↔ s.FiniteDimensional := by
  constructor
  · intro h
    let := h
    exact finiteDimensional_of_map hf
  · intro h
    let := h
    infer_instance

/-- An injective affine preimage of a finite-dimensional subspace is finite-dimensional. -/
theorem finiteDimensional_comap_of_injective {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    (t : AffineSubspace K Q) [t.FiniteDimensional] : (t.comap f).FiniteDimensional := by
  have : ((t.comap f).map f).FiniteDimensional :=
    finiteDimensional_of_le (map_comap_le f t)
  exact finiteDimensional_of_map hf

@[simp]
theorem finiteDimensional_map_equiv_iff (e : P ≃ᵃ[K] Q) :
    (s.map e.toAffineMap).FiniteDimensional ↔ s.FiniteDimensional :=
  finiteDimensional_map_iff e.injective

end Map

/-- Finite-dimensional affine subspaces are precisely the affine spans of finite sets. -/
theorem finiteDimensional_iff_exists_finite_affineSpan :
    s.FiniteDimensional ↔ ∃ S : Set P, S.Finite ∧ affineSpan K S = s := by
  constructor
  · intro hs
    let := hs
    obtain ⟨S, -, hS, hI⟩ := exists_affineIndependent K V (s : Set P)
    have hspan : affineSpan K S = s := hS.trans (affineSpan_coe s)
    have : (affineSpan K S).FiniteDimensional := hspan ▸ hs
    have : _root_.FiniteDimensional K (vectorSpan K (Set.range ((↑) : S → P))) := by
      rw [Subtype.range_coe, ← direction_affineSpan]
      exact (inferInstance : (affineSpan K S).FiniteDimensional)
    exact ⟨S, (finiteDimensional_iff_setFinite K hI).mp inferInstance, hspan⟩
  · rintro ⟨S, hS, rfl⟩
    exact finiteDimensional_affineSpan_of_finite hS

theorem finiteDimensional_iff_exists_finset_affineSpan :
    s.FiniteDimensional ↔ ∃ S : Finset P, affineSpan K (S : Set P) = s := by
  classical
  rw [finiteDimensional_iff_exists_finite_affineSpan]
  exact ⟨fun ⟨S, hS, hspan⟩ ↦ ⟨hS.toFinset, by simpa using hspan⟩,
    fun ⟨S, hspan⟩ ↦ ⟨S, S.finite_toSet, hspan⟩⟩

/-- The cardinal-valued dimension detects finite-dimensionality, including for `⊥`. -/
theorem finiteDimensional_iff_dim_lt_aleph0 :
    s.FiniteDimensional ↔ s.dim < (Cardinal.aleph0 : WithBot Cardinal) :=
  finite_iff_dim_lt_aleph0 s

/-- In finite dimension, the cardinal dimension is the natural dimension cast to cardinals.
This formulation also applies to the empty subspace. -/
theorem dim_eq_map_finDim [s.FiniteDimensional] :
    s.dim = s.finDim.map (fun n : ℕ ↦ (n : Cardinal)) := by
  rcases eq_or_ne s ⊥ with rfl | hs
  · simp
  rw [dim_eq_rank hs, finDim_eq_finrank hs, WithBot.map_natCast, WithBot.coe_inj]
  exact (Module.finrank_eq_rank' (K := K) (V := s.direction)).symm

/-- A finite-dimensional affine subspace is determined by inclusion and finite dimension. -/
theorem eq_of_le_of_finDim_eq [t.FiniteDimensional] (h : s ≤ t)
    (hd : s.finDim = t.finDim) : s = t := by
  by_contra hne
  exact (ne_of_lt (finDim_strictMono (lt_of_le_of_ne h hne))) hd

theorem finDim_eq_iff_eq_of_le [t.FiniteDimensional] (h : s ≤ t) :
    s.finDim = t.finDim ↔ s = t :=
  ⟨eq_of_le_of_finDim_eq h, fun h ↦ congrArg finDim h⟩

theorem lt_iff_finDim_lt_of_le [t.FiniteDimensional] (h : s ≤ t) :
    s < t ↔ s.finDim < t.finDim := by
  refine ⟨finDim_strictMono, fun hd ↦ lt_of_le_of_ne h ?_⟩
  intro heq
  exact (ne_of_lt hd) (congrArg finDim heq)

end AffineSubspace
