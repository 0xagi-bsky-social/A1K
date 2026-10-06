import SunflowerLean.Erdos20AxiomAudit

-- Intended trust-negative fixture, outside protected source closure.
axiom injectedPremise : False
theorem injectedTheorem : False := injectedPremise
#erdos20_audit injectedTheorem
