import Polyhedral.Toric.Mathlib.Geometry.Convex.Cone.Polyhedral



abbrev h (R N : Type*) [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup N]
    [Module R N] (C : PointedCone R N) :=
  PointedCone.IsPolyhedral C
