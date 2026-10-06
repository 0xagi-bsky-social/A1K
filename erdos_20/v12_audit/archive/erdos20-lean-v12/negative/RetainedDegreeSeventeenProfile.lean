import SunflowerLean.Erdos20V12ProfileReduction
-- The old boundary row (a,b,c,d)=(1,16,1,0) must not pass the new profile predicate.
example : Erdos20V12Profile.TwoCensusProfiles 16 1 0 := by
  unfold Erdos20V12Profile.TwoCensusProfiles
  decide
