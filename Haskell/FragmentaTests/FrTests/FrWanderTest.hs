
module FrWanderTest where

import FrUtils
import Grs
import SGrs
import Control.Monad(when)
import Utils
import LsFuns
import CheckUtils
import Frs

draw_aperson1 = do
   load_check_draw "Tests/f_APerson1.fr" "Tests/img/" 

draw_person1 = do
   load_check_draw "Tests/f_Person1.fr" "Tests/img/" 

fr_morph_1 =
   let mv = [("Person", "Person"), ("Hotel", "Other"), ("City", "Other"), ("Vehicle", "Other"), ("Name", "Other")] in
   let me = [("EHosts", "EAnyPersonRel"), 
             ("EOwns", "EAnyPersonRel"), 
             ("EPerson_lives", "EAnyPersonRel") ,
             ("EHotel_name", "EAnyOther"), 
             ("EPerson_name", "EAnyPersonRel")] in
   cons_gm mv me

main = do
   fif<-load_check_fr "Tests/f_Person1.fr"
   fia<-load_check_fr "Tests/f_APerson1.fr"
   when ((not $ isNil fif) && (not $ isNil fia)) $ do
      let (_, f) = theM fif
      let (_, af) = theM fia
      --putStrLn $ show f
      --check_morphism "Typing Morphism 1" WeakM fr_morph_1 f' af' True
      check_morphism "Morphism (weak model)" WeakM fr_morph_1 f af True
      check_morphism "Morphism (partial model)" PartialM fr_morph_1 f af True
      check_morphism "Morphism (total model)" (FullM Total) fr_morph_1 f af True
      --let b = is_wf_gm_frs Partial (fr_morph_1, f, af)
      --let b' = ok_frs  Partial f af
      --putStrLn $ show b
      --putStrLn $ show b'
      