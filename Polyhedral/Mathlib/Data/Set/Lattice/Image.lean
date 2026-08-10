/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Data.Set.Lattice.Image

/-!
This file contains results about images on sets.
-/

public section

open Function Set

namespace Set

theorem image_sInter_subset_sInf_image {α β : Type*} (S : Set (Set α)) (f : α → β) :
    f '' ⋂₀ S ⊆ sInf ((fun s => f '' s) '' S) := by
  rw [Set.sInf_eq_sInter, Set.sInter_image]
  exact Set.image_sInter_subset _ _

end Set
