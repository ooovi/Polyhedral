import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.ModularLattice
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

-- import Polyhedral.Mathlib.Algebra.Module.Submodule.Basic

namespace Submodule

open Function LinearMap Module

section Semiring

variable
  {S : Type*} [Semiring S]
  {R : Type*} [Semiring R] [Module S R]
  {M : Type*} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower S R M]
  -- {M : Type*} [AddCommMonoid M] [SMul S M] [Module R M] [IsScalarTower S R M]

lemma subtype_restrictScalars (p : Submodule R M) :
    p.subtype.restrictScalars S = (p.restrictScalars S).subtype := rfl

/- I suggest the alternative naming `restrict` for `submoduleOf` for the following reason:
  we want to have the same functionality on `PointedCone`, but there the name `submoduleOf`
  makes no sense. Using the same name is preferred for consistency.
  Note also that this cannot be an alias of `submoduleOf` because the argument are in the
  opposite order. This is in order to be consistent with `embed` for which the other order
  is not possible. This also allows us to view `restrict S` as the restriction operator.
  Finally, the "restrict" terminology is also used for e.g. `LinearMap.restrict`.
-/

-- NOTE: Something fundamental like this should probably be implemted somewhere more upstream
--  starting from monoids or so.

/-- The intersection `p ⊓ q` as a submodule of `p`. -/
abbrev restrict (p : Submodule R M) (q : Submodule S M) :
    Submodule S p := q.comap (p.subtype.restrictScalars S)

@[simp] lemma restrict_top (p : Submodule R M) :
    restrict p (⊤ : Submodule S M) = ⊤ := by simp [comap_top]
@[simp] lemma restrict_bot (p : Submodule R M) :
    restrict p (⊥ : Submodule S M) = ⊥ := by simp [comap_bot]

@[simp] lemma restrict_self (p : Submodule R M) :
    restrict p (p.restrictScalars S) = ⊤ := by ext; simp

lemma mem_restrict {p : Submodule R M} {q : Submodule S M} {x : p} (h : x ∈ restrict p q) :
    (x : M) ∈ q := by simpa using h

lemma mem_restrict_iff {p : Submodule R M} {q : Submodule S M} {x : p} :
    x ∈ restrict p q ↔ (x : M) ∈ q := by simp

lemma restrict_mono (p : Submodule R M) :
    Monotone (restrict p : Submodule S M → Submodule S p) := fun _ _ hrs => comap_mono hrs

lemma restrict_inf (p : Submodule R M) (q₁ q₂ : Submodule S M) :
    restrict p (q₁ ⊓ q₂) = (restrict p q₁) ⊓ (restrict p q₂)
  := by ext; simp

lemma restrict_sInf (p : Submodule R M) {s : Set (Submodule S M)} :
    restrict p (sInf s) = sInf (restrict p '' s)
  := by ext; simp

@[simp] lemma restrict_inf_self (p : Submodule R M) (q : Submodule S M) :
    restrict p (p.restrictScalars S ⊓ q) = restrict p q := by simp

lemma disjoint_restrict (p : Submodule R M) {q r : Submodule S M} (hqr : Disjoint q r) :
    Disjoint (restrict p q) (restrict p r) := by
  rw [disjoint_iff] at ⊢ hqr
  rw [← restrict_inf, hqr, restrict_bot]

lemma codisjoint_restrict_sup (p : Submodule R M) (q : Submodule R M) :
    Codisjoint (restrict (p ⊔ q) p) (restrict (p ⊔ q) q) := by
  rw [codisjoint_iff_exists_add_eq]
  intro x
  obtain ⟨y, hy, z, hz, h⟩ := mem_sup.mp x.2
  use ⟨y, mem_sup_left hy⟩, ⟨z, mem_sup_right hz⟩
  constructor
  · simp only [mem_restrict_iff, hy]
  constructor
  · simp only [mem_restrict_iff, hz]
  · simp only [AddMemClass.mk_add_mk, h]

def restrict_orderHom (p : Submodule R M) : Submodule S M →o Submodule S p where
  toFun := restrict p
  monotone' := restrict_mono p




/-- A submodule `q` of a submodule `p` of `M` as a submodule of `M`. -/
@[coe] abbrev embed {p : Submodule R M} (q : Submodule S p) : Submodule S M :=
    q.map (p.subtype.restrictScalars S)

@[simp] lemma mem_embed_iff {p : Submodule R M} {q : Submodule S p} {x : p} :
    (x : M) ∈ embed q ↔ x ∈ q := by simp

lemma mem_of_mem_embed {p : Submodule R M} {q : Submodule S p} {x : M} (hx : x ∈ embed q) :
    x ∈ p := by
  simp only [mem_map, LinearMap.coe_restrictScalars, subtype_apply, Subtype.exists,
    exists_and_right, exists_eq_right] at hx
  exact hx.choose

def of_mem_embed {p : Submodule R M} {q : Submodule S p} {x : M} (hx : x ∈ embed q) : p :=
  ⟨x, mem_of_mem_embed hx⟩

lemma of_mem_embed_mem {p : Submodule R M} {q : Submodule S p} {x : M} (hx : x ∈ embed q) :
    of_mem_embed hx ∈ q := by
  simp only [mem_map, LinearMap.coe_restrictScalars, subtype_apply, Subtype.exists,
    exists_and_right, exists_eq_right] at hx
  exact hx.choose_spec

@[simp] lemma embed_restrict (p : Submodule R M) (q : Submodule S M) :
    embed (restrict p q) = p.restrictScalars S ⊓ q := by
  simp [embed, restrict, subtype_restrictScalars, map_comap_subtype]

lemma embed_restrict_of_le {p : Submodule R M} {q : Submodule S M}
    (hpq : q ≤ p.restrictScalars S) : embed (restrict p q) = q := by
  nth_rw 2 [← inf_eq_right.mpr hpq]
  exact embed_restrict _ _

@[simp] lemma restrict_embed {p : Submodule R M} (q : Submodule S p) : restrict p (embed q) = q
    := by ext; simp

lemma restrict_surjective (p : Submodule R M) :
    Surjective (restrict p : Submodule S M → Submodule S p) := fun h => ⟨_, restrict_embed h⟩

lemma embed_injective {p : Submodule R M} : Injective (embed : Submodule S p → Submodule S M) :=
  map_injective_of_injective p.subtype_injective

@[simp] lemma embed_inj {p : Submodule R M} {q₁ q₂ : Submodule S p} :
    embed q₁ = embed q₂ ↔ q₁ = q₂ := Injective.eq_iff embed_injective

lemma embed_mono (p : Submodule R M) : Monotone (embed : Submodule S p → Submodule S M) :=
    fun _ _ h => Submodule.map_mono h

lemma embed_mono_rev {p : Submodule R M} {q₁ q₂ : Submodule S p} (hq : embed q₁ ≤ embed q₂) :
    q₁ ≤ q₂ := (by simpa using @hq ·)

@[simp] lemma embed_mono_iff {p : Submodule R M} {q₁ q₂ : Submodule S p} :
    embed q₁ ≤ embed q₂ ↔ q₁ ≤ q₂ where
  mp := embed_mono_rev
  mpr h := embed_mono p h

-- this should have higher priority than `map_top`
@[simp] lemma embed_top {p : Submodule R M} :
    embed (⊤ : Submodule S p) = p.restrictScalars S := by simp [subtype_restrictScalars]
@[simp] lemma embed_bot {p : Submodule R M} : embed (⊥ : Submodule S p) = ⊥ := map_bot _

@[simp] lemma embed_le {p : Submodule R M} {q : Submodule S p} :
    embed q ≤ p.restrictScalars S := by
  simpa [subtype_restrictScalars] using embed_mono p (le_top : q ≤ ⊤)

-- TODO: given this higher priority than `map_sup`
@[simp] lemma embed_sup {p : Submodule R M} (q r : Submodule S p) :
    embed (q ⊔ r) = embed q ⊔ embed r := map_sup _ _ _

@[simp] lemma embed_sup_left (p : Submodule R M) (q : Submodule S p) :
    embed q ⊔ p.restrictScalars S = p.restrictScalars S := sup_eq_right.mpr embed_le
@[simp] lemma embed_sup_right (p : Submodule R M) (q : Submodule S p) :
    p.restrictScalars S ⊔ embed q = p.restrictScalars S := sup_eq_left.mpr embed_le

lemma embed_iSup {ι : Type*} {p : Submodule R M} (f : ι → Submodule S p) :
    embed (⨆ i, f i) = ⨆ i, embed (f i) := map_iSup _ _

lemma embed_sSup {p : Submodule R M} (s : Set (Submodule S p)) :
    embed (sSup s) = sSup (embed '' s) := by
  unfold embed
  rw [subtype_restrictScalars]
  --rw [Submodule.map_iSup]
  --exact map_sSup
  --
  -- rw [sSup_eq_iSup]
  -- rw [sSup_eq_iSup]
  -- rw [embed_iSup]
  -- simp
  sorry

lemma embed_inf {p : Submodule R M} (q r : Submodule R p) :
    embed (q ⊓ r) = embed q ⊓ embed r := by
  simpa only [subtype_restrictScalars] using map_inf _ (subtype_injective _)

@[simp] lemma embed_inf_left (p : Submodule R M) (q : Submodule S p) :
    embed q ⊓ p.restrictScalars S = embed q := inf_eq_left.mpr embed_le
@[simp] lemma embed_inf_right (p : Submodule R M) (q : Submodule S p) :
    p.restrictScalars S ⊓ embed q = embed q := inf_eq_right.mpr embed_le

lemma embed_sInf {p : Submodule R M} (s : Set (Submodule S p)) :
    embed (sInf s) = sInf (embed '' s) := by sorry

    ---- <<< DONE UNTIL HERE

lemma embed_disjoint {p : Submodule R M} {q r : Submodule S p} (hqr : Disjoint q r) :
    Disjoint (embed q) (embed r) := by
  rw [disjoint_def] at ⊢ hqr
  intro x hxq hxr
  simpa using hqr (of_mem_embed hxq) (of_mem_embed_mem hxq) (of_mem_embed_mem hxr)

lemma embed_disjoint_iff {U : Submodule R M} {S T : Submodule R U} :
    Disjoint S T ↔ Disjoint (embed S) (embed T) := by
  constructor
  · exact embed_disjoint
  intro hST
  rw [disjoint_def] at ⊢ hST
  intro x hxS hxT
  simpa using hST x (mem_embed_iff.mpr hxS) (mem_embed_iff.mpr hxT)

lemma embed_codisjoint {U : Submodule R M} {S T : Submodule R U} (hST : Codisjoint S T) :
    embed S ⊔ embed T = U := by rw [← embed_sup, codisjoint_iff.mp hST, embed_top]

-- Q: Can this be expressed using LinearEquiv.ofInjective and subtype_injective?
def embed_equiv {p : Submodule R M} (q : Submodule S p) : q ≃ₗ[S] embed q := by
  let e := LinearEquiv.ofInjective _ p.subtype_injective
  exact e.restrictScalars S
  sorry

-- Q: Can this be expressed using LinearEquiv.ofInjective and subtype_injective?
def embed_equiv {S : Submodule R M} (T : Submodule R S) : T ≃ₗ[R] embed T where
  toFun x := ⟨S.subtype x, by simp⟩
  invFun x := ⟨⟨_, mem_of_mem_embed x.2⟩, mem_embed_iff.mp x.2⟩
  map_add' x y := by simp
  map_smul' r x := by simp
  left_inv x := by simp
  right_inv x := by simp

def restrict_equiv (S T : Submodule R M) : (S ⊓ T : Submodule R M) ≃ₗ[R] S.restrict T where
  toFun x := sorry
  invFun x := sorry
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

def embed_orderEmbed (S : Submodule R M) : Submodule R S ↪o Submodule R M where
  toFun := embed
  inj' := embed_injective
  map_rel_iff' := embed_mono_iff

def embed_latticeHom (S : Submodule R M) :
    CompleteLatticeHom (Submodule R S) (Submodule R M) where
  toFun := embed
  map_sInf' := embed_sInf
  map_sSup' := embed_sSup

def embed_gi (S : Submodule R M) : GaloisCoinsertion (embed) (restrict S) where
  choice := fun T _ => restrict S T
  gc T U := by simp [← embed_mono_iff, embed_restrict, le_inf_iff]
  u_l_le T := le_of_eq (restrict_embed T)
  choice_eq := by simp


-- ## QUOTIENT

section Ring

variable {M S R : Type*} [Ring R] [AddCommGroup M] [Module R M]

-- abbrev quot (S T : Submodule R M) := ...

/-- Second isomorphism theorem in terms of `Submodule.restrict` (see also
  `quotientInfEquivSupQuotient`). -/
noncomputable def quot_restrict_iso_sup_quot_restrict (S T : Submodule R M) :
    (S ⧸ restrict S T) ≃ₗ[R] (S ⊔ T : Submodule R M) ⧸ restrict (S ⊔ T) T := by
  rw [← restrict_inf_self, restrict_eq_comap_subtype]
  exact quotientInfEquivSupQuotient S T

/-- For a submodule `S` of `M` we can consider a quotient `S ⧸ T` as a submodule of `M ⧸ T`.
  Here we provide the canonical linear embeddig of `S ⧸ T` into `M ⧸ T`.
  See `quot_restrict_quot_linearMap_injective` for the proof of injectivity. -/
def quot_restrict_linearMap_quot (S T : Submodule R M) : S ⧸ restrict S T →ₗ[R] M ⧸ T :=
    liftQ _ (T.mkQ ∘ₗ S.subtype) (
      by simp [restrict_eq_comap_subtype, SetLike.le_def])

lemma quot_restrict_linearMap_quot_injective (S T : Submodule R M) :
    Injective (quot_restrict_linearMap_quot S T) := by
  rw [← ker_eq_bot]
  apply ker_liftQ_eq_bot
  simp [restrict_eq_comap_subtype, SetLike.le_def]

lemma quot_restrict_linearMap_quot_range (S T : Submodule R M) :
    range (quot_restrict_linearMap_quot S T) = map T.mkQ S := by
  ext x
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := h
    obtain ⟨z, hy⟩ := T.mkQ_surjective <| (quot_restrict_linearMap_quot S T) y
    use z
    constructor
    · sorry -- this does not hold, right?? We need a different proof.
    exact hy
  · intro h
    obtain ⟨_, hyS, rfl⟩ := h
    unfold quot_restrict_linearMap_quot
    exact ⟨(S.restrict T).mkQ ⟨_, hyS⟩, by simp⟩

-- noncomputable necessary? What if we also have T ≤ S?
noncomputable def quot_restrict_equiv_map_mkQ (S : Submodule R M) (T : Submodule R M) :
    (S ⧸ restrict S T) ≃ₗ[R] map T.mkQ S := by
  rw [← quot_restrict_linearMap_quot_range]
  exact .ofInjective _ (quot_restrict_linearMap_quot_injective S T)

-- TODO: noncomputable should not be necessary
noncomputable def quot_equiv_map_embed_mkQ (S : Submodule R M) (T : Submodule R S) :
    (S ⧸ T) ≃ₗ[R] map (embed T).mkQ S := by
  rw [← restrict_embed T, embed_restrict, embed_inf_right]
  simpa using quot_restrict_equiv_map_mkQ S (embed T)


end Ring

end Semiring

end Submodule
