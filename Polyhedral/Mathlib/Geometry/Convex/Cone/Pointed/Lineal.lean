
import Polyhedral.Mathlib.Geometry.Convex.Cone.Pointed.Basic

namespace PointedCone

open Module


section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- ## LINEAL

-- TODO: maybe lineal should be defined only over rings and via x ∈ C.lineal → -x ∈ C.lineal.
--   The given definition of lineal gives weird results over semiring such as the positive
--   elements of a ring. However, the current definition makes it very easy to see that it
--   is a submodule. The better definition is given as `lineal'` below.

/-- The lineality space of a cone. This is the set of all elements of the cone whose negative
  is also in the cone. The lineality space is a submodule. -/
def lineal (C : PointedCone R M) : Submodule R M := sSup {S : Submodule R M | S ≤ C }

def lineal_def (C : PointedCone R M) : C.lineal = sSup {S : Submodule R M | S ≤ C } := by rfl

/-- The lineality space is contained in the cone. -/
@[simp] lemma lineal_le (C : PointedCone R M) : C.lineal ≤ C := by simp [lineal]

/-- Every submodule contain int he cone is also contained in the lineality space. -/
lemma le_lineal {C : PointedCone R M} {S : Submodule R M} (hS : S ≤ C) :
    S ≤ C.lineal := le_sSup hS

alias submodule_le_lineal := le_lineal

lemma submodule_le_lineal_iff {C : PointedCone R M} {S : Submodule R M} :
  S ≤ C ↔ S ≤ C.lineal := ⟨submodule_le_lineal, fun h _ hx => C.lineal_le (h hx)⟩



end Semiring


section Ring

-----------------------
-- Better definition of lineal

variable {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

-- Q: Is this the better definition of `lineal`?
/-- The lineality space of a cone. -/
def lineal'' (C : PointedCone R M) : Submodule R M where
  carrier := {x ∈ C | ∃ y ∈ C, x + y = 0}
  add_mem' hx hy := by
    constructor
    · exact C.add_mem hx.1 hy.1
    obtain ⟨x', hx', hxx'⟩ := hx.2
    obtain ⟨y', hy', hyy'⟩ := hy.2
    use x' + y'
    constructor
    · exact C.add_mem hx' hy'
    nth_rw 2 [add_comm]
    rw [add_assoc]
    nth_rw 2 [← add_assoc]
    nth_rw 2 [add_comm]
    rw [← add_assoc]
    simp [hxx', hyy']
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp at *
    obtain ⟨x', hx', hxx'⟩ := hx.2
    by_cases hr : 0 ≤ r
    · constructor
      · exact C.smul_mem hr hx.1
      use r • x'
      constructor
      · exact C.smul_mem hr hx'
      simp [← smul_add, hxx']
    -- have H : r • x + r • x' = 0 := by sorry
    have H : ∃ r' ≥ 0, r + r' = 0 := sorry
    obtain ⟨r', hr', hrr'⟩ := H
    have H : r • x = r' • x' := sorry
    constructor
    · rw [H]
      exact C.smul_mem  hr' hx'
    have H' : r • x' = r' • x := sorry
    use r • x'
    constructor
    · simpa [H'] using C.smul_mem  hr' hx.1
    · simp [← smul_add, hxx']

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- Q: Is this the better definition of `lineal`?
/-- The lineality space of a cone. -/
def lineal' (C : PointedCone R M) : Submodule R M where
  carrier := C ∩ -C
  add_mem' hx hy := by simpa using ⟨C.add_mem hx.1 hy.1, C.add_mem hy.2 hx.2⟩
  zero_mem' := by simp
  smul_mem' r _ hx := by
    by_cases hr : 0 ≤ r
    · simpa using And.intro (C.smul_mem hr hx.1) (C.smul_mem hr hx.2)
    · have hr := le_of_lt <| neg_pos_of_neg <| lt_of_not_ge hr
      simpa using And.intro (C.smul_mem hr hx.2) (C.smul_mem hr hx.1)

@[simp] lemma lineal_eq_inter_neg' (C : PointedCone R M) : C.lineal' = C ⊓ -C := by rfl

lemma mem_lineal' {C : PointedCone R M} {x : M} : x ∈ C.lineal' ↔ x ∈ C ∧ -x ∈ C := by rfl

lemma lineal_le' (C : PointedCone R M) : C.lineal' ≤ C := by simp

lemma lineal_eq_sSup' (C : PointedCone R M) : C.lineal' = sSup {S : Submodule R M | S ≤ C } := by
  rw [le_antisymm_iff]
  constructor
  · exact le_sSup (lineal_le' C)
  intro x hx
  have hC : sSup {S : Submodule R M | S ≤ C} ≤ C := by simp
  exact mem_lineal'.mpr ⟨hC hx, hC (neg_mem hx : -x ∈ _)⟩

--------------------

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma neg_mem_of_mem_lineal {C : PointedCone R M} {x : M} (hx : x ∈ C.lineal) : -x ∈ C := by
  rw [← Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

lemma mem_of_neg_mem_lineal {C : PointedCone R M} {x : M} (hx : -x ∈ C.lineal) : x ∈ C := by
  rw [Submodule.neg_mem_iff] at hx
  exact lineal_le C hx

-- @[simp] -- no simp because right side has twice as many `x`?
-- i believe we need a linear order on R otherwise consider ℝ with the trivial order (i.e. the only
-- comparable elements are in ℤ), then ℤ ⊆ ℝ is a cone with x ∈ ℤ ↔ -x ∈ ℤ, but ℤ.lineal is trivial
lemma mem_lineal {C : PointedCone R M} {x : M} : x ∈ C.lineal ↔ x ∈ C ∧ -x ∈ C := by
  constructor
  · intro h
    have h' := neg_mem_iff.mpr h
    exact ⟨lineal_le C h, lineal_le C h'⟩
  · intro ⟨h, h'⟩
    let S := Submodule.span R {-x, x}
    have hSC : S ≤ C := by
      have hx : ({-x, x} : Set M) ⊆ C := by
        intro x hx
        obtain (rfl | rfl) := hx
        exact h'; exact h
      have hx := Submodule.span_mono (R := {c : R // 0 ≤ c}) hx
      simp at hx
      refine le_trans ?_ hx
      intro y hy
      apply Submodule.mem_span_pair.mp at hy
      rcases hy with ⟨a, b, hab⟩
      apply Submodule.mem_span_pair.mpr
      by_cases hab_pos : b≥a
      · use 0, ⟨b-a, sub_nonneg_of_le hab_pos⟩
        simp
        rw [← hab, sub_smul, sub_eq_add_neg, smul_neg, add_comm]
      have : a-b ≥ 0 := by
        sorry
      use ⟨a-b, this⟩, 0
      simp
      rw [← hab, ← smul_neg, sub_smul]
      simp
      -- simpa only [S, ← span_pm_pair_eq_submodule_span R] using hx
    have hSC := le_lineal hSC
    have hxS : x ∈ S := Submodule.mem_span_of_mem (by simp)
    exact hSC hxS -- maybe we could use the lemma that s ∪ -s spans a linear space (see above)

@[deprecated (since:="")]
alias lineal_mem := mem_lineal

def lineal_inf_neg (C : PointedCone R M) : C.lineal = C ⊓ -C := by
  ext x; simp [mem_lineal]

def lineal_mem_neg (C : PointedCone R M) : C.lineal = {x ∈ C | -x ∈ C} := by
  ext x; simp; exact mem_lineal

@[simp]
lemma lineal_inf (C D : PointedCone R M) : (C ⊓ D).lineal = C.lineal ⊓ D.lineal := by
  ext x; simp [mem_lineal]; aesop

@[simp] lemma lineal_submodule (S : Submodule R M) : (S : PointedCone R M).lineal = S := by
  ext x; simp [mem_lineal]

@[simp] lemma lineal_top : (⊤ : PointedCone R M).lineal = ⊤ := lineal_submodule ⊤
@[simp] lemma lineal_bot : (⊥ : PointedCone R M).lineal = ⊥ := lineal_submodule ⊥

lemma lineal_mono {C D : PointedCone R M} (h : C ≤ D) : C.lineal ≤ D.lineal := by
  intro x hx
  rw [mem_lineal] at *
  exact ⟨h hx.1, h hx.2⟩

/- In this section we show properties of lineal that also follow from lineal
  being a face. But we need this earlier than faces, so we need to prove that
  lineal is a face here. This can then be resused later.

  Alternatively, lineal can be defined in Faces.lean
-/

lemma lineal_isExtreme_left {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal := by
  have hxy' := neg_mem_of_mem_lineal hxy
  have hx' := C.add_mem hy hxy'
  simp only [neg_add_rev, add_neg_cancel_left] at hx'
  exact mem_lineal.mpr ⟨hx, hx'⟩

lemma lineal_isExtreme_right {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : y ∈ C.lineal := by
  rw [add_comm] at hxy; exact lineal_isExtreme_left hy hx hxy

lemma lineal_isExtreme {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : x + y ∈ C.lineal) : x ∈ C.lineal ∧ y ∈ C.lineal :=
  ⟨lineal_isExtreme_left hx hy hxy, lineal_isExtreme_right hx hy hxy⟩

lemma lineal_isExtreme_right_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  have h := lineal_isExtreme_right hx (C.smul_mem (le_of_lt hc) hy) hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_left_of_inv {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hc' : Invertible c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  have h := lineal_isExtreme_left (C.smul_mem (le_of_lt hc) hx) hy hxy
  simpa using C.lineal.smul_mem (Invertible.invOf c) h

lemma lineal_isExtreme_sum {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (h : ∑ x ∈ xs, x ∈ C.lineal) : (xs : Set M) ⊆ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.sum_insert hy] at *
    have h := lineal_isExtreme hxs.1 (C.sum_mem hxs.2) h
    exact ⟨h.1, H hxs.2 h.2⟩

@[simp] lemma sup_lineal_eq (C : PointedCone R M) : C ⊔ C.lineal = C :=
    sup_of_le_left (lineal_le C)

-- NOTE: equality holds, e.g., if D is a face of C
lemma lineal_sup_le (C D : PointedCone R M) : C.lineal ⊔ D.lineal ≤ (C ⊔ D).lineal := by
  intro x
  simp only [Submodule.mem_sup, mem_lineal, forall_exists_index, and_imp]
  intro y hy hy' z hz hz' rfl
  exact ⟨⟨y, hy, by use z⟩, -y, hy', -z, hz', by simp [add_comm]⟩

-- ## PRIORITY
--isnt this false when C and D are two rays pointing in opposite directions?
lemma _lineal_sup_eq (C D : PointedCone R M) (hCD : C.linSpan ⊓ D.lineal ≤ C.lineal) :
    (C ⊔ D).lineal = C.lineal ⊔ D.lineal := by
  rw [le_antisymm_iff, and_comm]
  constructor
  · exact lineal_sup_le ..
  intro x
  simp [Submodule.mem_sup, mem_lineal]
  simp [SetLike.le_def, mem_lineal, mem_linSpan] at hCD
  intro y hy z hz hyz w hw v hv hwv
  have h := hCD
  sorry


-- lemma sup_lineal (C : PointedCone R M) (S : Submodule R M) : S ≤ (C ⊔ S).lineal := sorry

-- !! only holds over fields or archimedean rings! Not in general.
lemma mem_lineal_of_smul_mem_lineal' {C : PointedCone R M} :
  (∀ c > 0, ∃ d > 0, d * c ≥ 1) ↔ (∀ x ∈ C, ∀ c > 0, c • x ∈ C.lineal → x ∈ C.lineal) := sorry

-- !! only holds over fields or archimedean rings! Not in general.
lemma mem_lineal_of_smul_mem_lineal {C : PointedCone R M} {x : M} {c : R}
    (hx : x ∈ C) (hcx : c • x ∈ C.lineal) : x ∈ C.lineal := by
  wlog h0c : 0 ≤ c
  · sorry
  · wlog h1c : 1 ≤ c with H
    · --have H := @H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (1+1) hx
      sorry
    · have h : c = c - 1 + 1 := by simp
      rw [h] at hcx
      clear h
      rw [add_smul] at hcx
      simp at hcx
      have h' : 1 ≤ c ↔ 0 ≤ c - 1 := by simp
      rw [h'] at h1c
      replace h' := smul_mem C h1c hx
      exact lineal_isExtreme_right h' hx hcx


-- Q: Can we shorten the proof, see `inf_sup_lineal_eq_of_isCompl` below.
/-- If `C` is a cone and `S` is complementary to the cone's linealiry space, then `C` can
  be written as `(C ⊓ S) ⊔ C.lineal`. -/
lemma inf_sup_lineal {C : PointedCone R M} {S : Submodule R M} (hCS : Codisjoint C.lineal S) :
    (C ⊓ S) ⊔ C.lineal = C := by
  rw [le_antisymm_iff]
  constructor
  · exact sup_le_iff.mpr ⟨inf_le_left, lineal_le C⟩
  · intro x hx
    rw [Submodule.codisjoint_iff_exists_add_eq] at hCS
    obtain ⟨y, z, hy, hz, hyz⟩ := hCS x
    rw [Submodule.mem_sup]
    have hzC : z ∈ C := by
      have h := Submodule.add_mem C hx (neg_mem_of_mem_lineal hy)
      rw [← hyz, add_neg_cancel_comm] at h
      exact h
    exact ⟨z, by simp; exact ⟨hzC, hz⟩, y, hy, by rw [add_comm]; exact hyz⟩

@[deprecated inf_sup_lineal (since := "2025-11-07")]
lemma inf_sup_lineal_eq_of_isCompl {C : PointedCone R M} {S : Submodule R M}
    (hCS : IsCompl S C.lineal) : (C ⊓ S) ⊔ C.lineal = C := by
  simp [← inf_sup_assoc_of_submodule_le S (lineal_le C), ← coe_sup,
    codisjoint_iff.mp hCS.codisjoint]



-- ## MAP

open Function LinearMap

variable {N : Type*} [AddCommGroup N] [Module R N]

lemma map_lineal_le (C : PointedCone R M) (f : M →ₗ[R] N) :
    C.lineal.map f ≤ (C.map f).lineal := by
  intro y
  simp [mem_lineal]
  intro x hx hmx hfxy
  exact ⟨⟨x, hx, hfxy⟩, ⟨-x, hmx, by rw [← hfxy, LinearMap.map_neg]⟩⟩

lemma map_lineal (C : PointedCone R M) {f : M →ₗ[R] N} (hf : Injective f) :
    (C.map f).lineal = C.lineal.map f := by
  rw [le_antisymm_iff]
  constructor
  · intro x
    simp [mem_lineal]
    intro y hy hfxy z hz hfxz
    use y
    · constructor
      · constructor
        · exact hy
        rw [← hfxy, ← LinearMap.map_neg] at hfxz
        simpa [← hf hfxz] using hz
      · exact hfxy
  · exact map_lineal_le C f

lemma comap_lineal (C : PointedCone R M) {f : N →ₗ[R] M} :
    (C.comap f).lineal = C.lineal.comap f := by
  ext x; simp [mem_lineal]

@[simp] lemma neg_lineal (C : PointedCone R M) : (-C).lineal = C.lineal := by
  simp [← comap_id_eq_neg, comap_lineal]



lemma lineal_restrict (S : Submodule R M) (C : PointedCone R M) :
    (restrict S C).lineal = .restrict S C.lineal := by
  simp only [Submodule.submoduleOf, ← comap_lineal, ← Submodule.subtype_restrictScalars, comap]

lemma lineal_embed (S : Submodule R M) (C : PointedCone R S) :
    (embed C).lineal = .embed C.lineal := by simp [map_lineal]




end Ring


section DivisionRing

variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma lineal_isExtreme_left' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : c • x + y ∈ C.lineal) : x ∈ C.lineal := by
  exact lineal_isExtreme_left_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_right' {C : PointedCone R M} {x y : M} (hx : x ∈ C) (hy : y ∈ C)
    {c : R} (hc : 0 < c) (hxy : x + c • y ∈ C.lineal) : y ∈ C.lineal := by
  exact lineal_isExtreme_right_of_inv hx hy hc (invertibleOfNonzero <| ne_of_gt hc) hxy

lemma lineal_isExtreme_sum' {C : PointedCone R M} {xs : Finset M} (hxs : (xs : Set M) ⊆ C)
    (c : M → R) (hc : ∀ x ∈ xs, 0 < c x) (h : ∑ x ∈ xs, c x • x ∈ C.lineal) :
    ∀ x ∈ xs, c x ≠ 0 → x ∈ C.lineal := by classical
  induction xs using Finset.induction_on with
  | empty => simp
  | insert y xs hy H =>
    simp only [Set.subset_def, Finset.mem_coe, SetLike.mem_coe, ne_eq, Finset.coe_insert,
      Set.mem_insert_iff, forall_eq_or_imp, Finset.mem_insert, Finset.sum_insert hy] at *
    have hxsC := C.sum_mem (fun x hx => C.smul_mem (le_of_lt <| hc.2 x hx) (hxs.2 x hx))
    constructor
    · exact fun _ => lineal_isExtreme_left' hxs.1 hxsC hc.1 h
    · exact H hxs.2 hc.2 <| lineal_isExtreme_right (C.smul_mem (le_of_lt hc.1) hxs.1) hxsC h

variable (R) in
lemma span_inter_lineal_eq_lineal (s : Set M) :
    span R (s ∩ (span R s).lineal) = (span R s).lineal := by
  rw [le_antisymm_iff]
  constructor
  · rw [← Submodule.span_eq <| ofSubmodule ((span R s).lineal)]
    refine Submodule.span_mono ?_
    simp only [Submodule.coe_restrictScalars, Set.inter_subset_right]
  · sorry
  -- constructor
  -- · rw [← Submodule.span_eq (C.lineal : PointedCone R M)]
  --   exact Submodule.span_mono (by simp)
  -- · rw [← SetLike.coe_subset_coe]
  --   rw [Set.subset_def]
  --   intro x hx
  --   let S:= s ∩ C.lineal
  --   let S' := s \ C.lineal
  --   have hS : S ∪ S' = s := by simp [S, S']
  --   have hS' : S ∩ S' = ∅ := by aesop

  --   --have hs : s = (s ∩ C.lineal) ∪ ()
  --   -- rw [Submodule.mem_span_finite_of_mem_span] at h
    -- sorry

lemma FG.lineal_fg {C : PointedCone R M} (hC : C.FG) : C.lineal.FG := by classical
  obtain ⟨s, hs⟩ := hC
  use (s.finite_toSet.inter_of_left C.lineal).toFinset -- means {x ∈ s | x ∈ C.lineal}
  rw [submodule_span_of_span]
  simpa [← hs] using span_inter_lineal_eq_lineal R (s : Set M)

end DivisionRing



section Ring

-- ## SALIENT

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

-- TODO: definition should probably be formulated without negation: x ∈ C → x = 0
/-- A salient cone has trivial lineality space, see `salient_iff_lineal_bot`. -/
abbrev Salient (C : PointedCone R M) := C.toConvexCone.Salient

lemma salient_iff_mem_neg {C : PointedCone R M} : C.Salient ↔ ∀ x ∈ C, x ≠ 0 → -x ∉ C := by rfl

lemma Salient.mem_neg_mem_zero {C : PointedCone R M} (hC : C.Salient)
    {x : M} (hx : x ∈ C) (hx' : -x ∈ C) : x = 0 := by
  specialize hC x hx
  rw [not_imp_not] at hC
  exact hC hx'

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma salient_iff_lineal_bot {C : PointedCone R M} : C.Salient ↔ C.lineal = ⊥ := by
  constructor
  · intro h
    ext x
    simp only [mem_lineal, Submodule.mem_bot]
    exact ⟨fun H => h.mem_neg_mem_zero H.1 H.2, by simp +contextual⟩
  · intro h x hx
    rw [not_imp_not]
    intro hnx
    have hlin := mem_lineal.mpr ⟨hx, hnx⟩
    rw [h] at hlin
    exact hlin

/-- If `S` is a submodule disjoint to the lineality space of a cone `C`, then `C ⊓ S`
  is salient. -/
lemma inf_salient {C : PointedCone R M} {S : Submodule R M} (hCS : Disjoint C.lineal S) :
    (C ⊓ S).Salient := by
  simp only [salient_iff_lineal_bot, lineal_inf, lineal_submodule, ← disjoint_iff, hCS]

@[deprecated inf_salient (since := "...")]
lemma inf_salient_of_disjoint {C : PointedCone R M}
    {S : Submodule R M} (hS : C.lineal ⊓ S = ⊥) : (C ⊓ S).Salient := by
  simpa [salient_iff_lineal_bot] using hS

lemma Salient.of_le_salient {C D : PointedCone R M} (hC : C.Salient) (hD : D ≤ C) : D.Salient := by
  rw [Salient, ConvexCone.salient_iff_not_flat] at *
  by_contra h
  apply hC
  rcases h with ⟨x, xD, x_ne_0, neg_xD⟩
  exact ⟨x, hD xD, x_ne_0, hD neg_xD⟩
  -- have h' := h.mono hD

-- ## MAP

open Function

variable {N : Type*} [AddCommGroup N] [Module R N]

omit [LinearOrder R] [IsOrderedRing R] in
-- TODO: generalize and move to the right place
@[simp] lemma injective_neg {f : N →ₗ[R] M} : Injective (-f) ↔ Injective f := by
  simp [Injective]

omit [LinearOrder R] [IsOrderedRing R] in
@[simp] lemma surjective_neg {f : N →ₗ[R] M} : Surjective (-f) ↔ Surjective f := by
  constructor
  · exact fun h x => by simpa using h (-x)
  · intro h x
    obtain ⟨y, hy⟩ := h (-x)
    exact ⟨y, by simp [hy]⟩

---

lemma salient_map {C : PointedCone R M} {f : M →ₗ[R] N} (hC : C.Salient) (hf : Injective f) :
    (C.map f).Salient := by
  rw [salient_iff_lineal_bot] at *
  simp [map_lineal _ hf, hC]

lemma salient_comap {C : PointedCone R M} {f : N →ₗ[R] M} (hC : C.Salient) (hf : Injective f) :
    (C.comap f).Salient := by
  rw [salient_iff_lineal_bot] at *
  simpa [comap_lineal, hC] using LinearMap.ker_eq_bot_of_injective hf

lemma salient_neg {C : PointedCone R M} (hC : C.Salient) : (-C).Salient := by
  simpa [← map_id_eq_neg] using salient_map hC (injective_neg.mpr injective_id)



-- section DivisionRing

-- variable {R : Type*} [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
-- variable {M : Type*} [AddCommGroup M] [Module R M]

-- /-- A pointed cone can be written as a sup of its lineality space and a complementary
--   salient cone. -/
-- lemma exists_salient_disj_sup_lineal (C : PointedCone R M) :
--     ∃ D : PointedCone R M, D.Salient
--       ∧ Disjoint C.lineal (.span R D)
--       ∧ D ⊔ C.lineal = C := by
--   have ⟨S, hDis, hCod⟩ := exists_isCompl C.lineal
--   refine ⟨C ⊓ S, inf_salient hDis, Disjoint.mono_right ?_ hDis, inf_sup_lineal hCod⟩
--   rw [← Submodule.span_eq (p := S)]
--   exact Submodule.span_mono (by simp)

-- /-- A pointed cone can be written as a sup of a submodule and a complementary
--   salient cone. -/
-- lemma exists_salient_submodul_disj_sup (C : PointedCone R M) :
--     ∃ D : PointedCone R M, D.Salient ∧
--       ∃ S : Submodule R M, Disjoint S (.span R D) ∧ D ⊔ S = C := by
--   obtain ⟨D, hSal, hDis, hSup⟩ := exists_salient_disj_sup_lineal C
--   exact ⟨D, hSal, C.lineal, hDis, hSup⟩

-- end DivisionRing



-- ## SALIENT QUOT

variable {C : PointedCone R M}

/-- The quotient of a cone by its lineality space. -/
abbrev salientQuot (C : PointedCone R M) := C.quot C.lineal

lemma salientQuot_def (C : PointedCone R M) : C.salientQuot = C.quot C.lineal := rfl

lemma salient_salientQuot (C : PointedCone R M) : Salient C.salientQuot := by
  rw [Salient, ConvexCone.salient_iff_not_flat]
  intro h
  rcases h with ⟨x, hx, x_ne_0, hx'⟩
  rcases (Set.mem_image (⇑C.lineal.mkQ) (↑C) x).mp hx with ⟨y,yC, hy⟩
  rcases (Set.mem_image (⇑C.lineal.mkQ) (↑C) (-x)).mp hx' with ⟨y',yC', hy'⟩
  have : y ∉ C.lineal := by
    intro h
    apply x_ne_0
    rw [← hy]
    simp [h]
  apply this
  have : (C.lineal).mkQ (y+y') = 0 := by
    rw [map_add, hy, hy', add_neg_cancel]
  have sum_lineal : y+y' ∈ C.lineal := by
    rw [← Submodule.ker_mkQ C.lineal]
    exact LinearMap.mem_ker.mpr this
  apply mem_lineal.mp at sum_lineal
  have : -y ∈ C := by
    have : y' + -(y + y') = -y := by
      simp
    rw [← this]
    exact Submodule.add_mem C yC' (sum_lineal.2)
  exact mem_lineal.mpr ⟨yC, this⟩

@[simp] lemma salientQuot_of_submodule (S : Submodule R M) :
    (S : PointedCone R M).salientQuot = ⊥ := by
  unfold salientQuot
  rw [lineal_submodule, ← Submodule.span_eq S]
  simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  rw [← ofSubmodule_coe, quot_span]

lemma salientQuot_fg (hC : C.FG) : C.salientQuot.FG := quot_fg hC _

-- def salientQuot_neg (C : PointedCone R M) : C.salientQuot ≃ₗ[R] (-C).salientQuot := sorry

--variable (R M) in
/-- Salient rank of a cone. -/
noncomputable def salRank (C : PointedCone R M) := C.salientQuot.rank
    -- Module.rank R (Submodule.span R (C.salientQuot : Set (M ⧸ C.lineal)))

--variable (R M) in
/-- Salient rank of a cone. -/
noncomputable def salFinrank (C : PointedCone R M) := C.salientQuot.finrank
    -- Module.finrank R (Submodule.span R (C.salientQuot : Set (M ⧸ C.lineal)))

abbrev FinSalRank (C : PointedCone R M) := FinRank C.salientQuot

end Ring

end PointedCone
