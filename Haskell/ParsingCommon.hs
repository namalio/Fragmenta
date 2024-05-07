module ParsingCommon (
   parse_id
   , parseNumber
   , parseMaybe
   , parse_until_chs
   , parse_ls_ids
   , capitalise_fst
   , lower_fst
   , parseIdLoose) where

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

parse_id::ReadP String
parse_id = do
   ch<- satisfy (isLetter)
   str<-munch is_val_id_char
   return (ch:str)

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
parse_until_chs chs = do manyTill (satisfy (\ch->True)) (satisfyWLook (\c-> any (c ==) chs))

parse_ls_ids ::String->ReadP [String]
parse_ls_ids sep = do
   ps<-sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep) >> skipSpaces)
   --ps<-sepBy (parse_id) (skipSpaces>>satisfy (\ch->any (ch==) sep))
   -- parses last id
   --p<-parse_id
   return ps --(ps++[p])

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