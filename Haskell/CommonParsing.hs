module CommonParsing (parse_id, parse_spc_id, parse_number, parseMaybe, parse_until_chs, parse_ls_ids, capitalise_fst, lower_fst) where

import Text.ParserCombinators.ReadP
import qualified Data.Char as Char

is_letter::Char->Bool
is_letter ch = (ch>='a' && ch<='z') || (ch>='A' && ch<='Z')

is_digit::Char->Bool
is_digit ch = (ch>='0' && ch<='9') 

is_val_id_char::Char->Bool
is_val_id_char ch = is_letter ch || is_digit ch || ch == '_'

parse_number::ReadP String
parse_number = do
   n<- (many1 . satisfy) is_digit
   return n

-- parse_fst_letter_of_id ::ReadP String
-- parse_fst_letter_of_id = do
--   ch<- satisfy (is_letter)
--   return (ch:"")

parse_id::ReadP String
parse_id = do
   ch<- satisfy (is_letter)
   str<-(munch is_val_id_char)
   return (ch:str)

parse_spc_id::ReadP String
parse_spc_id = do
   skipSpaces
   id<-parse_id
   return (id)

parseMaybe :: ReadP a -> String -> Maybe a
parseMaybe parser input =
    case readP_to_S parser input of
        [] -> Nothing
        ((result, _):_) -> Just result

parse_until_chs::String->ReadP String
parse_until_chs chs = do
    str<-manyTill (satisfy (\ch->True)) (satisfy (\ch-> any (ch ==) chs))
    return str

parse_ls_ids ::String->ReadP [String]
parse_ls_ids sep = do
   ps<-sepBy (parse_spc_id) (satisfy (\ch->any (ch==) sep))
   -- parses last id
   p<-parse_spc_id
   return (ps++[p])

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