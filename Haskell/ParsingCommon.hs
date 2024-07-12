module ParsingCommon (
   parseId
   , parseNumber
   , parseMaybe
   , parse_until_chs
   , parse_ls_ids
   , capitalise_fst
   , lower_fst
   , parseIdLoose
   , parse_strings
   , parseWord
   , parseAnyStr) where

import Text.ParserCombinators.ReadP
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
   ch<- satisfy (isLetter)
   str<-munch is_val_id_char
   return (ch:str)

parseWord::ReadP String
parseWord = munch is_val_id_char

parseAnyStr::String->ReadP String
parseAnyStr stchs = munch (\ch->ch `notElem` ([' ', '\n', '\t', '@'] ++ stchs))

parseIdLoose::ReadP String
parseIdLoose = munch is_val_id_char

--parse_spc_id::ReadP String
--parse_spc_id = do
--   skipSpaces
--   id<-parse_id
--   return (id)

parseMaybe :: ReadP a -> String -> Maybe a
parseMaybe parser input =
    case readP_to_S parser input of
        [] -> Nothing
        ((result, _):_) -> Just result

satisfyWLook::(Char->Bool)->ReadP Char
satisfyWLook p = look >>= (\s->if not (null s) && p (head s) then return (head s) else pfail)

parse_until_chs::String->ReadP String
parse_until_chs chs = do manyTill (get) (satisfyWLook (\c-> any (c ==) chs))



parse_strings ::String->ReadP String->ReadP [String]
parse_strings sep sparser = do
   sepBy (sparser) (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)

parse_ls_ids ::String->ReadP [String]
parse_ls_ids sep = parse_strings sep parseId
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

test3 = readP_to_S (parse_ls_ids ",") "ABC , CDE"

--test4 :: [([String], String)]
--test4 = readP_to_S ((\sep->sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)) ",") "ABC , CDE"