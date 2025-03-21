module ParsingCommon (
   parseId
   , parseNumber
   , parseMaybe
   , parse_until_chs
   , parseIds
   , capitalise_fst
   , lower_fst
   , parseIdLoose
   , parseTokens
   , parseWord
   , parseAnyStr
   , satisfyWLook) where

import Text.ParserCombinators.ReadP
    ( ReadP,
      (<++),
      get,
      look,
      many1,
      manyTill,
      munch,
      pfail,
      readP_to_S,
      satisfy,
      sepBy,
      skipSpaces,
      string,
      eof)
import qualified Data.Char as Char
import MyMaybe ( str_of_ostr )
import ParseUtils ( isDigit )

isLetter::Char->Bool
isLetter ch = ch `elem` ['a'..'z'] || ch `elem` ['A'..'Z']

is_val_id_char::Char->Bool
is_val_id_char ch = isLetter ch || isDigit ch || ch == '_'

parseNumber::ReadP String
parseNumber = (many1 . satisfy) isDigit

-- parse_fst_letter_of_id ::ReadP String
-- parse_fst_letter_of_id = do
--   ch<- satisfy (is_letter)
--   return (ch:"")

parseId::ReadP String
parseId = do
   ch<- satisfy isLetter
   str<-munch is_val_id_char
   return (ch:str)

parseWord::ReadP String
parseWord = munch is_val_id_char

parseAnyStr::String->ReadP String
parseAnyStr stchs = munch (`notElem` stchs)

-- Check this out later
--parseQStr::String->ReadP String
--parseQStr stchs = do
--   char '\"'
--   s<-parse_until_chs "\""
--   char '\"'
--   return s

parseIdLoose::ReadP String
parseIdLoose = munch is_val_id_char

--parse_spc_id::ReadP String
--parse_spc_id = do
--   skipSpaces
--   id<-parse_id
--   return (id)

parseMaybe :: ReadP a -> String -> Maybe a
parseMaybe parser input = 
    case readP_to_S (parser <* eof) input of
        [] -> Nothing
        ((r, _):_) -> Just r


satisfyWLook::(Char->Bool)->ReadP Char
satisfyWLook p = look >>= (\s->if not (null s) && p (head s) then return (head s) else pfail)

parse_until_chs::String->ReadP String
parse_until_chs chs = 
   manyTill (get) (satisfyWLook (\c-> any (c ==) chs))

parseTokens ::String->ReadP a->ReadP [a]
parseTokens sep parser = do
   sepBy parser (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)

parseIds ::String->ReadP [String]
parseIds sep = parseTokens sep parseId
--   ps<-sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)
   --ps<-sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep))
   -- parses last id
   --p<-parse_id
--   return ps --(ps++[p])

parse_either_strs::[String]->ReadP String
parse_either_strs (s:ss) = do
    str<- string s <++ parse_either_strs ss
    return str

capitalise_fst::String->String
capitalise_fst "" = ""
capitalise_fst (c:cs) = (Char.toUpper c):cs

lower_fst::String->String
lower_fst "" = ""
lower_fst (c:cs) = (Char.toLower c):cs

test1 = readP_to_S (parse_until_chs ".,") "ABC.CDE"
test2 = readP_to_S (parse_until_chs ".,") "ABC,CDE"

test3 = readP_to_S (parseIds ",") "ABC , CDE"

test4 :: [(String, String)]
test4 = readP_to_S (parseAnyStr "") "{intoHall}"

--test4 :: [([String], String)]
--test4 = readP_to_S ((\sep->sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)) ",") "ABC , CDE"