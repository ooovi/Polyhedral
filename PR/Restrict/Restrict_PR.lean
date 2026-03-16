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

variable {M S R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

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

/-- The restriction of `S ⊓ T` reinterpreted as a submodule of `S`. -/
abbrev restrict (S T : Submodule R M) : Submodule R S := T.submoduleOf S -- T.comap S.subtype

-- Q: Shoud have `restrict` as an order hom? If yes, use the code below.
-- def restrict' (S : Submodule R M) : Submodule R M →o Submodule R S where
--   toFun := (submoduleOf · S)
--   monotone' := fun _ _ h _ => (h ·)

lemma restrict_eq_comap_subtype (S T : Submodule R M) :
    restrict S T = Submodule.comap S.subtype T := rfl

@[simp] lemma restrict_top (S : Submodule R M) : restrict S ⊤ = ⊤ := by
  simp only [submoduleOf, comap_top]
@[simp] lemma restrict_bot (S : Submodule R M) : restrict S ⊥ = ⊥ := by
  simp only [submoduleOf, comap_bot, ker_subtype]

@[simp] lemma restrict_self (S : Submodule R M) : restrict S S = ⊤ := submoduleOf_self S

lemma mem_restrict {S : Submodule R M} {T : Submodule R M} {x : S} (h : x ∈ restrict S T) :
    (x : M) ∈ T := by simpa using h

lemma mem_restrict_iff {S : Submodule R M} {T : Submodule R M} {x : S} :
    x ∈ restrict S T ↔ (x : M) ∈ T := by simp [submoduleOf]

-- TODO: use `Monotone`
lemma restrict_mono (S : Submodule R M) {T₁ T₂ : Submodule R M} (hCD : T₁ ≤ T₂) :
    restrict S T₁ ≤ restrict S T₂ := fun _ => (hCD ·)

lemma restrict_inf (S : Submodule R M) {T₁ T₂ : Submodule R M} :
    restrict S (T₁ ⊓ T₂) = (restrict S T₁) ⊓ (restrict S T₂)
  := by ext x; simp [restrict, submoduleOf]

lemma restrict_sInf (S : Submodule R M) {t : Set (Submodule R M)} :
    restrict S (sInf t) = sInf (restrict S '' t)
  := by ext x; simp [restrict, submoduleOf]

@[simp] lemma restrict_inf_self (S T : Submodule R M) :
    restrict S (S ⊓ T) = restrict S T := by simp [restrict_inf]

lemma restrict_disjoint (U : Submodule R M) {S T : Submodule R M} (hST : Disjoint S T) :
    Disjoint (restrict U S) (restrict U T) := by
  rw [disjoint_iff] at *
  rw [← restrict_inf, hST, restrict_bot]

lemma codisjoint_restrict_sup (S T : Submodule R M) :
    Codisjoint (restrict (S ⊔ T) S) (restrict (S ⊔ T) T) := by
  rw [codisjoint_iff_exists_add_eq]
  intro x
  obtain ⟨y, hy, z, hz, h⟩ := mem_sup.mp x.2
  use ⟨y, mem_sup_left hy⟩
  use ⟨z, mem_sup_right hz⟩
  constructor
  · simp only [mem_restrict_iff, hy]
  constructor
  · simp only [mem_restrict_iff, hz]
  · simp only [AddMemClass.mk_add_mk, h]

-- `Submodule.mapIic` is a weird and hard to look up name.
example (S : Submodule R M) : Submodule R S ≃o Set.Iic S := Submodule.mapIic S

def restrict_orderHom (S : Submodule R M) : Submodule R M →o Submodule R S where
  toFun := restrict S
  monotone' _ _ := restrict_mono S



-- TODO: remove the `abbrev`? It should never be unfolded I think
/-- A submodule `T` of a submodule `S` of `M` reintepreted as a submodule of `M`. -/
@[coe] abbrev embed {S : Submodule R M} (T : Submodule R S) : Submodule R M := T.map S.subtype

-- Q: Shoud have `embed` as an order embedding? If yes, use the code below.
-- def embed_orderEmbed {S : Submodule R M} : Submodule R S ↪o Submodule R M where
--   toFun := map S.subtype
--   inj' := map_injective_of_injective S.subtype_injective
--   map_rel_iff' := ⟨fun h x => by simpa using @h x, Submodule.map_mono⟩

@[simp] lemma mem_embed_iff {S : Submodule R M} {T : Submodule R S} {x : S} :
    (x : M) ∈ embed T ↔ x ∈ T := by simp

lemma mem_of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    x ∈ S := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨hxS, _⟩ := hx
  exact hxS

abbrev of_mem_embed {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) : S :=
  ⟨x, mem_of_mem_embed hx⟩

lemma of_mem_embed_mem {S : Submodule R M} {T : Submodule R S} {x : M} (hx : x ∈ embed T) :
    of_mem_embed hx ∈ T := by
  simp only [mem_map, subtype_apply, Subtype.exists, exists_and_right, exists_eq_right] at hx
  obtain ⟨_, h⟩ := hx
  exact h

@[simp] lemma embed_restrict (S T : Submodule R M) : embed (restrict S T) = S ⊓ T
  := map_comap_subtype _ _

lemma embed_restrict_of_le {S T : Submodule R M} (hST : T ≤ S) :
    embed (restrict S T) = T := by
  nth_rw 2 [← inf_eq_right.mpr hST]
  exact embed_restrict S T

@[simp] lemma restrict_embed {S : Submodule R M} (T : Submodule R S) : restrict S (embed T) = T
    := by ext x; simp [submoduleOf]

def restrict_surjective (S : Submodule R M) : Surjective (restrict S) := (⟨_, restrict_embed ·⟩)

lemma embed_injective {S : Submodule R M} : Injective (embed : Submodule R S → Submodule R M)
  := map_injective_of_injective S.subtype_injective

@[simp] lemma embed_inj {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ = embed T₂ ↔ T₁ = T₂ := Injective.eq_iff embed_injective

-- TODO: use `Monotone`
lemma embed_mono {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : T₁ ≤ T₂) :
    embed T₁ ≤ embed T₂ := Submodule.map_mono hT

lemma embed_mono_rev {S : Submodule R M} {T₁ T₂ : Submodule R S} (hT : embed T₁ ≤ embed T₂) :
    T₁ ≤ T₂ := (by simpa using @hT ·)

@[simp] lemma embed_mono_iff {S : Submodule R M} {T₁ T₂ : Submodule R S} :
    embed T₁ ≤ embed T₂ ↔ T₁ ≤ T₂ where
  mp := embed_mono_rev
  mpr := embed_mono

-- this should have higher priority than `map_top`
@[simp] lemma embed_top {S : Submodule R M} : embed (⊤ : Submodule R S) = S := by simp
@[simp] lemma embed_bot {S : Submodule R M} : embed (⊥ : Submodule R S) = ⊥ := map_bot _

@[simp] lemma embed_le {S : Submodule R M} {T : Submodule R S} : embed T ≤ S := by
  simpa using embed_mono le_top

-- TODO: given this higher priority than `map_sup`
@[simp] lemma embed_sup {U : Submodule R M} (S T : Submodule R U) :
    embed (S ⊔ T) = embed S ⊔ embed T := map_sup _ _ _

@[simp] lemma embed_sup_left (S : Submodule R M) (T : Submodule R S) :
    embed T ⊔ S = S := sup_eq_right.mpr embed_le
@[simp] lemma embed_sup_right (S : Submodule R M) (T : Submodule R S) :
    S ⊔ embed T = S := sup_eq_left.mpr embed_le

lemma embed_iSup {ι : Type*} {U : Submodule R M} (f : ι → Submodule R U) :
    embed (⨆ i, f i) = ⨆ i, embed (f i) := map_iSup _ _

lemma embed_sSup {U : Submodule R M} (s : Set (Submodule R U)) :
    embed (sSup s) = sSup (embed '' s) := by
  -- rw [sSup_eq_iSup]
  -- rw [sSup_eq_iSup]
  -- rw [embed_iSup]
  -- simp
  sorry

lemma embed_inf {U : Submodule R M} (S T : Submodule R U) :
    embed (S ⊓ T) = embed S ⊓ embed T := map_inf _ (subtype_injective _)

@[simp] lemma embed_inf_left (S : Submodule R M) (T : Submodule R S) :
    embed T ⊓ S = embed T := inf_eq_left.mpr embed_le
@[simp] lemma embed_inf_right (S : Submodule R M) (T : Submodule R S) :
    S ⊓ embed T = embed T := inf_eq_right.mpr embed_le

lemma embed_sInf {U : Submodule R M} (s : Set (Submodule R U)) :
    embed (sInf s) = sInf (embed '' s) := by sorry

lemma embed_disjoint {U : Submodule R M} {S T : Submodule R U} (hST : Disjoint S T) :
    Disjoint (embed S) (embed T) := by
  rw [disjoint_def] at ⊢ hST
  intro x hxS hxT
  simpa using hST (of_mem_embed hxS) (of_mem_embed_mem hxS) (of_mem_embed_mem hxT)

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
