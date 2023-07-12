module FragmentaTests.GTests.GTestsCommon
where

import Grs ( consG, Gr )
import Sets (set, singles)
import TheNil

def_path :: String
def_path = "FragmentaTests/GTests/"
img_path :: String
img_path = "FragmentaTests/GTests/img/"

-- Two malformed graphs
eg1 :: Gr String String
eg1 = 
   let ns' = set ["A", "B"] in
   let es' = singles "EAB" in
   let s = set  [("EAB", "A")] in 
   let t = nil in
   consG ns' es' s t

eg2 :: Gr String String
eg2 = 
   let ns' = set ["A", "B"] in
   let es' = singles "EAB" in
   let s = set [("EAB", "C")] in 
   let t = set [("EAB", "B")] in
   consG ns' es' s t

eg3 :: Gr String String
eg3 = 
   let ns' = set ["V1", "V2", "V3", "V4"] in
   let es' = set ["EV1V2", "EV2V3", "EV3V4"] in
   let s = set [("EV1V2", "V1"), ("EV2V3", "V2"), ("EV3V4", "V3")] in 
   let t = set [("EV1V2", "V2"), ("EV2V3", "V3"), ("EV3V4", "V4")] in
   consG ns' es' s t

eg4 :: Gr String String
eg4 = 
   let ns' = singles "V1" in
   let es' = singles "EV1V1" in
   let s = singles ("EV1V1", "V1") in
   let t = singles ("EV1V1", "V1") in
   consG ns' es' s t