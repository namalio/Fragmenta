
module ParseUtils(
   words'
   , splitAt'
   , splitAtStr
   , isDigit
   , isInt
   , isReal) where

import SimpleFuns

isDigit::Char->Bool
isDigit ch = ch `elem` ['0'..'9'] 

isInt :: String -> Bool
isInt s = 
   (not . null $ s) && (head s == '-' || isDigit (head s)) &&  all isDigit (tail s)

isReal :: String -> Bool
isReal s = 
   let (wn, dn) = splitAt' (=='.') s in
   (null wn || isInt wn) && isInt dn

words' :: (Char->Bool)-> String -> [String]
words' isSep [] = []
words' isSep (xxs@(x:xs))
  | isSep x   = words' isSep xs
  | otherwise =  ys : words' isSep rest
      where (ys, rest) = break (isSep) xxs

splitAt' :: (a -> Bool) -> [a] -> ([a], [a])
splitAt' p [] = ([], [])
splitAt' p (x:xs) 
   | p x = ([], xs)
   | otherwise = (x:ys, ys')
      where (ys, ys') = splitAt' p xs

splitAtStr :: Eq a => [a] -> [a] -> ([a], [a])
splitAtStr _ [] = ([], [])
splitAtStr s xs@(x:xs') 
   | s `equalLs` (take (length s) xs) = ([], drop (length s) xs)
   | otherwise = (x:ys, ys')
      where (ys, ys') = splitAtStr s xs'

--do_indent :: (Eq t, Num t) => t -> [Char]
--do_indent 0 = ""
--do_indent n = "   " ++ do_indent(n-1)

-- Writes elements separated by some separator
-- Takes an identation level (a natural number)
--wrSepElems:: (Eq t, Num t)=>[String] -> String -> Bool -> Bool -> t -> String
--wrSepElems [] _ _ _ _ = ""
--wrSepElems (s:ss) sep spaced ind i
--   | (null ss) = (if ind then (do_indent i) else "") ++ s
--   | otherwise = 
--   let spc = if spaced then " " else "" in
--   let dind = if ind then do_indent i else "" in
--      dind++s++sep++spc++(wrSepElems ss sep spaced False i)
