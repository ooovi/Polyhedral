
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.RingTheory.Finiteness.Basic

open Function
open Submodule

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]
variable {B : Type*} [AddTorsor W B]

def _root_.AffineMap.range (f : A →ᵃ[R] B) : AffineSubspace R B := sorry -- {f x | (x : A)}

variable {R : Type*} [Ring R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A W) in
class AffineHomogenization where
  embed : A →ᵃ[R] W
  ne_zero : 0 ∉ embed.range
  span_top : span R (embed.range : Set W) = ⊤

namespace AffineHomogenization

variable [hom : AffineHomogenization R A W]

-- def linEmbed : V →ₗ[R] W := hom.embed.linear

-- def atInfinity : Submodule R W := linEmbed.range

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {A : Type*} [AddTorsor V A]
variable {W : Type*} [AddCommGroup W] [Module R W]

variable (R A) in
def AffineSpace.eval : A →ᵃ[R] ((A →ᵃ[R] R) →ₗ[R] R) := sorry

lemma zero_not_mem_eval_rang : 0 ∉ (AffineSpace.eval R A).range := sorry

abbrev AffineSubspace.affineHomogenization_of_zero_not_mem {A : AffineSubspace R V} [Nonempty A]
    (h : 0 ∉ A) : AffineHomogenization R A (span R (A : Set V)) where
  embed := sorry
  ne_zero := sorry
  span_top := sorry

variable (R A) in
abbrev canonicalHomogenization := (A →ᵃ[R] R) →ₗ[R] R

-- variable (R A) in
-- def canonicalHomogenization := span R ((AffineSpace.eval R A).range : Set ((A →ᵃ[R] R) →ₗ[R] R))

instance canonicalHomogenization_affineHomogenization :
    AffineHomogenization R A (canonicalHomogenization R A) where
  embed := AffineSpace.eval R A
  ne_zero := zero_not_mem_eval_rang
  span_top := sorry

end AffineHomogenization
