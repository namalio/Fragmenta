module NumString() where
import Gr_Cls
import ParseUtils

strToInt::String->Maybe Int
strToInt s =
   let (h, ns) = splitAt' (`elem` ['v', 'V']) s in 
   if isInt ns && null h then Just (read ns::Int) else Nothing

strToReal::String->Maybe Float
strToReal s =
   let (h, ns) = splitAt' (`elem` ['v', 'V']) s in 
   if isReal ns && null h then Just (read ns::Float) else Nothing

instance GNodesNumConv String where
   toInt = strToInt
   toReal = strToReal

instance GNumSets String where
   nNatS = "Nat"
   nIntS = "Int"
   nRealS = "Real"