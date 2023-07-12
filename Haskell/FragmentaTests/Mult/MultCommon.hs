module FragmentaTests.Mult.MultCommon where

import Sets (Set, set )

r1 :: Set (String, String)
r1 = set [("A1", "B1"), ("A2", "B2")]
r1_s1 :: (Set (String, String), Set String, Set String)
r1_s1 = (r1, set ["A1", "A2"], set ["B1", "B2"])
r1_s2 :: (Set (String, String), Set String, Set String)
r1_s2 = (r1, set ["A1", "A2", "A3"], set ["B1", "B2"])

r2 :: Set (String, String)
r2 = set [("A1", "B1"), ("A2", "B2"), ("A2", "B3")]
r2_s1 :: (Set (String, String), Set String, Set String)
r2_s1 = (r2, set ["A1", "A2"], set ["B1", "B2", "B3", "B4"])
r2_s2 :: (Set (String, String), Set String, Set String)
r2_s2 = (r2, set ["A1", "A2", "A3"], set ["B1", "B2", "B3", "B4"])

r3 :: Set (String, String)
r3 = set [("A1", "B1"), ("A1", "B2")]
r3_s1 = (r3, set ["A1", "A2", "A3"], set ["B1", "B2", "B3", "B4"])

r4 = set [("A1", "B1"), ("A2", "B2")]
r4_s1 = (r4, set ["A1", "A2", "A3"], set ["B1", "B2", "B3", "B4"])