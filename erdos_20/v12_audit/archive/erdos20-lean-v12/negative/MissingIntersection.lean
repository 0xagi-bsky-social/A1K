import SunflowerLean.Erdos20Incidence
example : ∀ S ∈ Erdos20Incidence.twoTriangles, ∀ T ∈ Erdos20Incidence.twoTriangles, (S ∩ T).Nonempty := by decide
