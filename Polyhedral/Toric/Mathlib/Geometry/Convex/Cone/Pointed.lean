import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.RingTheory.Finiteness.Basic

namespace PointedCone
variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E]
  [Module 𝕜 E] {S : Set E}

variable (𝕜 S) in
/-- The span of a set `S` is the smallest pointed cone that contains `S`.

Pointed cones being defined as submodules over nonnegative scalars, this is exactly the
submodule span of `S` w.r.t. nonnegative scalars. -/
abbrev span : PointedCone 𝕜 E := Submodule.span _ S

lemma subset_span : S ⊆ PointedCone.span 𝕜 S := Submodule.subset_span

abbrev ofSubmodule (S : Submodule 𝕜 E) : PointedCone 𝕜 E := S.restrictScalars _

instance : Coe (Submodule 𝕜 E) (PointedCone 𝕜 E) := ⟨ ofSubmodule ⟩

lemma ofSubmodule.eq (S : Submodule 𝕜 E) : (ofSubmodule S : Set E) = S :=
  Submodule.coe_restrictScalars 𝕜 S

variable {𝕜 E : Type*} [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

local notation "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

lemma span_span_eq_restrictedScalar_span (S : Set E) :
    PointedCone.span 𝕜 (Submodule.span 𝕜 S)
      = Submodule.restrictScalars 𝕜≥0 (Submodule.span 𝕜 S) := by simp

lemma Submodule.span_span_eq_span_pos_sup_span_neg (S : Set E) :
    PointedCone.span 𝕜 (Submodule.span 𝕜 S) = PointedCone.span 𝕜 S ⊔ PointedCone.span 𝕜 (-S) := by
  rw [Submodule.ext_iff]
  intro x; simp
  rw [Submodule.mem_sup] -- Submodule.mem_sup'
  rw [Submodule.mem_span_set']
  constructor
  · intro hx
    obtain ⟨ n, f, g, hfg ⟩ := hx
    let fp : Fin n → 𝕜≥0 := fun k => ⟨ max 0 ( f k), by simp ⟩
    let fn : Fin n → 𝕜≥0 := fun k => ⟨ max 0 (-f k), by simp ⟩
    let xp :=  ∑ i, fp i • (g i).val
    let xn := -∑ i, fn i • (g i).val
    use xp; constructor
    · rw [Submodule.mem_span_set']
      use n; use fp; use g
    use xn; constructor
    · rw [Submodule.mem_span_set']
      use n; use fn; use (fun k => ⟨ -(g k).val, by simp ⟩) -- easier?
      simp [xn]
    simp [xp, xn, fp, fn]
    -- rw [Finset.sum_union]
    sorry
  · intro hx
    obtain ⟨ xp, hxp, xn, hxn, h ⟩ := hx
    rw [Submodule.mem_span_set'] at *
    obtain ⟨ np, fp, gp, hp ⟩ := hxp
    obtain ⟨ nn, fn, gn, hn ⟩ := hxn
    let n := np + nn
    let f : Fin n → 𝕜 := Fin.append (fun k => (fp k).1) (fun k => (fn k).1)
    let g : Fin n → S := Fin.append gp (fun k => ⟨ -(gn k).1, by -- easier?
      have H : (gn k).val ∈ -S := by simp
      simp [-Subtype.coe_prop] at H
      exact H ⟩ )
    use n; use f; use g
    sorry

lemma Submodule.restrictScalars_pos_span_eq_span_pos_union_neg (S : Set E) :
    .restrictScalars 𝕜≥0 (Submodule.span 𝕜 S) = PointedCone.span 𝕜 (S ∪ -S) := by
   -- PointedCone.span 𝕜 (Submodule.span 𝕜 S) = PointedCone.span 𝕜 (S ∪ -S) := by
  rw [←Submodule.span_coe_eq_restrictScalars]
  rw [span, Submodule.span_union]
  exact span_span_eq_span_pos_sup_span_neg S

lemma ofSubmodule.FG_of_FG {S : Submodule 𝕜 E} (h : S.FG) : (S : PointedCone 𝕜 E).FG := by
  rw [Submodule.fg_def] at *
  obtain ⟨ F, hFin, hSpan ⟩ := h
  use F ∪ -F
  constructor
  · simp; exact hFin
  · rw [←hSpan];
    exact (Submodule.restrictScalars_pos_span_eq_span_pos_union_neg F).symm

end PointedCone
