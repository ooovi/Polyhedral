/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Polyhedral.Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Finite-dimensional affine subspaces

`AffineSubspace.FiniteDimensional s` means that the direction of `s` is finite-dimensional.
It is an abbreviation, just as `FiniteDimensional` is an abbreviation for `Module.Finite`.
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

/-- An affine subspace is finite-dimensional if its direction is finite-dimensional.
In particular, the empty affine subspace is finite-dimensional. -/
abbrev FiniteDimensional (s : AffineSubspace K P) : Prop :=
  _root_.FiniteDimensional K s.direction

variable {s t : AffineSubspace K P}

theorem finiteDimensional_iff_direction :
    s.FiniteDimensional ↔ _root_.FiniteDimensional K s.direction := Iff.rfl

/-- A nonempty affine subspace has the same finite-dimensionality as its underlying affine
space. This comparison is a theorem, not an instance. -/
theorem finiteDimensional_iff_affineSpace (s : AffineSubspace K P) [Nonempty s] :
    s.FiniteDimensional ↔ AffineSpace.FiniteDimensional K s := Iff.rfl

theorem dim_eq_affine_dim (s : AffineSubspace K P) [Nonempty s] :
    s.dim = (AffineSpace.dim K s : WithBot Cardinal) :=
  dim_eq_rank (nonempty_iff_ne_bot s |>.mp (Set.nonempty_coe_sort.mp inferInstance))

theorem finDim_eq_affine_finDim (s : AffineSubspace K P) [Nonempty s] :
    s.finDim = (AffineSpace.finDim K s : WithBot ℕ) :=
  finDim_eq_finrank (nonempty_iff_ne_bot s |>.mp (Set.nonempty_coe_sort.mp inferInstance))

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

theorem finiteDimensional_toAffineSubspace (S : Submodule K V)
    (hS : _root_.FiniteDimensional K S) : S.toAffineSubspace.FiniteDimensional :=
  (finiteDimensional_toAffineSubspace_iff S).mpr hS

theorem finiteDimensional_mk' (p : P) (S : Submodule K V)
    (hS : _root_.FiniteDimensional K S) : (mk' p S).FiniteDimensional := by
  unfold FiniteDimensional
  rw [direction_mk']
  exact hS

/-- Every affine subspace of a finite-dimensional ambient space is finite-dimensional. -/
theorem finiteDimensional_of_finiteDimensional
    [AffineSpace.FiniteDimensional K P] (s : AffineSubspace K P) : s.FiniteDimensional :=
  inferInstanceAs (_root_.FiniteDimensional K s.direction)

theorem finiteDimensional_bot : (⊥ : AffineSubspace K P).FiniteDimensional := by
  unfold FiniteDimensional
  rw [direction_bot]
  infer_instance

/-- Finite-dimensionality descends to affine subspaces. -/
theorem finiteDimensional_of_le (ht : t.FiniteDimensional) (h : s ≤ t) :
    s.FiniteDimensional := by
  let := ht
  exact Submodule.finiteDimensional_of_le (direction_le h)

theorem finiteDimensional_inf_left (s t : AffineSubspace K P) (hs : s.FiniteDimensional) :
    (s ⊓ t).FiniteDimensional :=
  finiteDimensional_of_le hs inf_le_left

theorem finiteDimensional_inf_right (s t : AffineSubspace K P) (ht : t.FiniteDimensional) :
    (s ⊓ t).FiniteDimensional :=
  finiteDimensional_of_le ht inf_le_right

/-- An indexed intersection is finite-dimensional if one of its members is. -/
theorem finiteDimensional_iInf {ι : Sort*} (S : ι → AffineSubspace K P) (i : ι)
    (hi : (S i).FiniteDimensional) : (⨅ j, S j).FiniteDimensional :=
  finiteDimensional_of_le hi (iInf_le S i)

theorem finiteDimensional_finset_sup {ι : Type*} (I : Finset ι)
    (S : ι → AffineSubspace K P) (hS : ∀ i ∈ I, (S i).FiniteDimensional) :
    (I.sup S).FiniteDimensional := by
  refine Finset.sup_induction finiteDimensional_bot ?_ hS
  intro s hs t ht
  let := hs
  let := ht
  infer_instance

theorem finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι → AffineSubspace K P)
    (hS : ∀ i, (S i).FiniteDimensional) : (⨆ i, S i).FiniteDimensional := by
  classical
  let := Fintype.ofFinite (PLift ι)
  simpa only [Finset.sup_univ_eq_iSup, iSup_plift_down] using
    finiteDimensional_finset_sup Finset.univ (fun i : PLift ι ↦ S i.down) (fun i _ ↦ hS i.down)

/-- A singleton is finite-dimensional, even in an infinite-dimensional ambient space. -/
theorem finiteDimensional_singleton (p : P) : ({p} : AffineSubspace K P).FiniteDimensional :=
  inferInstance

/-- Binary joins preserve finite-dimensionality. -/
theorem finiteDimensional_sup_of_finiteDimensional (hs : s.FiniteDimensional)
    (ht : t.FiniteDimensional) : (s ⊔ t).FiniteDimensional := by
  let := hs
  let := ht
  infer_instance

/-- The affine span of a finite set is finite-dimensional. -/
theorem finiteDimensional_affineSpan_of_finite {S : Set P} (hS : S.Finite) :
    (affineSpan K S).FiniteDimensional :=
  finiteDimensional_direction_affineSpan_of_finite K hS

theorem finiteDimensional_affineSpan_finset (S : Finset P) :
    (affineSpan K (S : Set P)).FiniteDimensional :=
  finiteDimensional_affineSpan_of_finite S.finite_toSet

/-- The affine span of a subset of a finite-dimensional subspace is finite-dimensional. -/
theorem finiteDimensional_affineSpan_of_subset (hs : s.FiniteDimensional) {S : Set P}
    (hS : S ⊆ s) : (affineSpan K S).FiniteDimensional :=
  finiteDimensional_of_le hs (affineSpan_le.mpr hS)

section Map

variable {W Q : Type*} [AddCommGroup W] [Module K W] [AddTorsor W Q]

theorem finiteDimensional_map (hs : s.FiniteDimensional) (f : P →ᵃ[K] Q) :
    (s.map f).FiniteDimensional := by
  let := hs
  infer_instance

/-- Finite-dimensionality descends along an injective affine map. -/
theorem finiteDimensional_of_map {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    (hs : (s.map f).FiniteDimensional) : s.FiniteDimensional := by
  have : _root_.FiniteDimensional K (s.direction.map f.linear) := by
    rw [← map_direction]
    exact hs
  exact (Submodule.equivMapOfInjective f.linear
    (f.linear_injective_iff.mpr hf) s.direction).symm.finiteDimensional

theorem finiteDimensional_map_iff {f : P →ᵃ[K] Q} (hf : Function.Injective f) :
    (s.map f).FiniteDimensional ↔ s.FiniteDimensional := by
  constructor
  · exact finiteDimensional_of_map hf
  · exact fun h ↦ finiteDimensional_map h f

/-- An injective affine preimage of a finite-dimensional subspace is finite-dimensional. -/
theorem finiteDimensional_comap_of_injective {f : P →ᵃ[K] Q} (hf : Function.Injective f)
    (t : AffineSubspace K Q) (ht : t.FiniteDimensional) : (t.comap f).FiniteDimensional :=
  finiteDimensional_of_map hf (finiteDimensional_of_le ht (map_comap_le f t))

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
theorem dim_eq_map_finDim (hs : s.FiniteDimensional) :
    s.dim = s.finDim.map (fun n : ℕ ↦ (n : Cardinal)) := by
  let := hs
  rcases eq_or_ne s ⊥ with rfl | hbot
  · simp
  rw [dim_eq_rank hbot, finDim_eq_finrank hbot, WithBot.map_natCast, WithBot.coe_inj]
  exact (Module.finrank_eq_rank' (K := K) (V := s.direction)).symm

/-- A finite-dimensional affine subspace is determined by inclusion and finite dimension. -/
theorem eq_of_le_of_finDim_eq (ht : t.FiniteDimensional) (h : s ≤ t)
    (hd : s.finDim = t.finDim) : s = t := by
  let := ht
  by_contra hne
  exact (ne_of_lt (finDim_strictMono (lt_of_le_of_ne h hne))) hd

theorem finDim_eq_iff_eq_of_le (ht : t.FiniteDimensional) (h : s ≤ t) :
    s.finDim = t.finDim ↔ s = t :=
  ⟨eq_of_le_of_finDim_eq ht h, fun h ↦ congrArg finDim h⟩

theorem lt_iff_finDim_lt_of_le (ht : t.FiniteDimensional) (h : s ≤ t) :
    s < t ↔ s.finDim < t.finDim := by
  let := ht
  refine ⟨finDim_strictMono, fun hd ↦ lt_of_le_of_ne h ?_⟩
  intro heq
  exact (ne_of_lt hd) (congrArg finDim heq)

end AffineSubspace
