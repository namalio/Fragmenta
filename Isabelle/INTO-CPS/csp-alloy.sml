structure CSP_Alloy : sig
  type num
  type int
  type nat
  datatype exp = Expid of char list | Expapp of exp * exp list | Exppar of exp |
    Num of int | PlusExp of exp * exp | MinusExp of exp * exp |
    GtExp of exp * exp | GtEqExp of exp * exp | LtExp of exp * exp |
    LtEqExp of exp * exp | Srange of exp * exp | Ext of exp list |
    Prfx of exp * exp | STOP | SKIP | Let_within of decl list * exp |
    If_then_else of exp * exp * exp | SeqComp of exp * exp |
    Interleave of exp * exp | Parallel of exp * exp * exp list |
    IntChoice of exp * exp | ExtChoice of exp * exp | RepExtChoice of stmt * exp
  and decl = Channel of (char list) list | Eqdecl of exp * exp |
    Assert of exp * exp
  and stmt = Stmt of char list * exp
  type nibble
  datatype aExp = AExpid of char list | AExpset of aExp | AExpTrcl of aExp |
    AExpno of aExp | AExpthis | AExpIdn | AExpnone | AExpeq of aExp * aExp |
    AExpneq of aExp * aExp | AExpDot of aExp * aExp | AExpPlus of aExp * aExp |
    AExpAnd of aExp * aExp
  datatype mult = Mlone | Mone | Msome
  datatype declExp = Dset of mult option * aExp
  datatype decla = Dc of (char list) list * declExp
  datatype sigTy = Sabstract | Snormal
  datatype cSPSpec = Csp of decl list
  datatype sigDecl =
    Sig of
      sigTy * mult option * (char list) list * (char list) option * decla list *
        aExp list
  datatype factDecl = Fact of char list * aExp list
  datatype checkDecl = Check of char list * nat
  datatype assertDecl = Asserta of char list * aExp list
  datatype alloyParagraph = Psig of sigDecl | Pfact of factDecl |
    Passert of assertDecl | Pcheck of checkDecl
  datatype alloyModule = Amodule of char list * alloyParagraph list
  type 'a gr_ls_ext
  type 'a fr_ls_ext
  type 'a morph_ext
  type 'a mdl_ls_ext
  type 'a morphL_ext
  type 'a tyMdl_ls_ext
  type 'a mdlTy_ls_ext
  val str_nat : nat -> char list
  val str_int : int -> char list
  val toCSP : unit gr_ls_ext -> cSPSpec
  val toAlloy : unit gr_ls_ext -> alloyModule
  val mdlTy_3WTs : unit mdlTy_ls_ext
  val mdlL : 'a mdlTy_ls_ext -> unit mdl_ls_ext
  val mtyL : 'a mdlTy_ls_ext -> unit morphL_ext
  val iNTO_SysML_toPDG : unit mdlTy_ls_ext -> unit gr_ls_ext
  val mdlTy_3WTs_loop : unit mdlTy_ls_ext
  val cSP_output_dir : char list
  val alloy_output_dir : char list
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

datatype int = Zero_int | Pos of num | Neg of num;

val one_inta : int = Pos One;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One One = Bit0 One;

fun uminus_int (Neg m) = Pos m
  | uminus_int (Pos m) = Neg m
  | uminus_int Zero_int = Zero_int;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun dup (Neg n) = Neg (Bit0 n)
  | dup (Pos n) = Pos (Bit0 n)
  | dup Zero_int = Zero_int;

fun plus_inta (Neg m) (Neg n) = Neg (plus_num m n)
  | plus_inta (Neg m) (Pos n) = sub n m
  | plus_inta (Pos m) (Neg n) = sub m n
  | plus_inta (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_inta Zero_int l = l
  | plus_inta k Zero_int = k
and sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) (Pos One)
  | sub (Bit1 m) (Bit0 n) = plus_inta (dup (sub m n)) (Pos One)
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub (Bit0 m) One = Pos (bitM m)
  | sub One One = Zero_int
and minus_int (Neg m) (Neg n) = sub n m
  | minus_int (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_int (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_int (Pos m) (Pos n) = sub m n
  | minus_int Zero_int l = uminus_int l
  | minus_int k Zero_int = k;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = Zero_int} : int zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  int numeral;

fun times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
  | times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n)
  | times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n))
  | times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n))
  | times_num One n = n
  | times_num m One = m;

fun times_inta (Neg m) (Neg n) = Pos (times_num m n)
  | times_inta (Neg m) (Pos n) = Neg (times_num m n)
  | times_inta (Pos m) (Neg n) = Neg (times_num m n)
  | times_inta (Pos m) (Pos n) = Pos (times_num m n)
  | times_inta Zero_int l = Zero_int
  | times_inta k Zero_int = Zero_int;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : int semiring;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  int mult_zero;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : int semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : int monoid_mult;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : int semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : int semiring_1;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

val equal_char = {equal = (fn a => fn b => ((a : char) = b))} : char equal;

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) equal;

datatype sGETy = Einh | Ecompbi | Ecompuni | Erelbi | Ereluni | Elnk | Eref;

fun equal_SGETya Elnk Eref = false
  | equal_SGETya Eref Elnk = false
  | equal_SGETya Ereluni Eref = false
  | equal_SGETya Eref Ereluni = false
  | equal_SGETya Ereluni Elnk = false
  | equal_SGETya Elnk Ereluni = false
  | equal_SGETya Erelbi Eref = false
  | equal_SGETya Eref Erelbi = false
  | equal_SGETya Erelbi Elnk = false
  | equal_SGETya Elnk Erelbi = false
  | equal_SGETya Erelbi Ereluni = false
  | equal_SGETya Ereluni Erelbi = false
  | equal_SGETya Ecompuni Eref = false
  | equal_SGETya Eref Ecompuni = false
  | equal_SGETya Ecompuni Elnk = false
  | equal_SGETya Elnk Ecompuni = false
  | equal_SGETya Ecompuni Ereluni = false
  | equal_SGETya Ereluni Ecompuni = false
  | equal_SGETya Ecompuni Erelbi = false
  | equal_SGETya Erelbi Ecompuni = false
  | equal_SGETya Ecompbi Eref = false
  | equal_SGETya Eref Ecompbi = false
  | equal_SGETya Ecompbi Elnk = false
  | equal_SGETya Elnk Ecompbi = false
  | equal_SGETya Ecompbi Ereluni = false
  | equal_SGETya Ereluni Ecompbi = false
  | equal_SGETya Ecompbi Erelbi = false
  | equal_SGETya Erelbi Ecompbi = false
  | equal_SGETya Ecompbi Ecompuni = false
  | equal_SGETya Ecompuni Ecompbi = false
  | equal_SGETya Einh Eref = false
  | equal_SGETya Eref Einh = false
  | equal_SGETya Einh Elnk = false
  | equal_SGETya Elnk Einh = false
  | equal_SGETya Einh Ereluni = false
  | equal_SGETya Ereluni Einh = false
  | equal_SGETya Einh Erelbi = false
  | equal_SGETya Erelbi Einh = false
  | equal_SGETya Einh Ecompuni = false
  | equal_SGETya Ecompuni Einh = false
  | equal_SGETya Einh Ecompbi = false
  | equal_SGETya Ecompbi Einh = false
  | equal_SGETya Eref Eref = true
  | equal_SGETya Elnk Elnk = true
  | equal_SGETya Ereluni Ereluni = true
  | equal_SGETya Erelbi Erelbi = true
  | equal_SGETya Ecompuni Ecompuni = true
  | equal_SGETya Ecompbi Ecompbi = true
  | equal_SGETya Einh Einh = true;

val equal_SGETy = {equal = equal_SGETya} : sGETy equal;

datatype sGNTy = Nnrml | Nabst | Nprxy | Nenum;

fun equal_SGNTya Nprxy Nenum = false
  | equal_SGNTya Nenum Nprxy = false
  | equal_SGNTya Nabst Nenum = false
  | equal_SGNTya Nenum Nabst = false
  | equal_SGNTya Nabst Nprxy = false
  | equal_SGNTya Nprxy Nabst = false
  | equal_SGNTya Nnrml Nenum = false
  | equal_SGNTya Nenum Nnrml = false
  | equal_SGNTya Nnrml Nprxy = false
  | equal_SGNTya Nprxy Nnrml = false
  | equal_SGNTya Nnrml Nabst = false
  | equal_SGNTya Nabst Nnrml = false
  | equal_SGNTya Nenum Nenum = true
  | equal_SGNTya Nprxy Nprxy = true
  | equal_SGNTya Nabst Nabst = true
  | equal_SGNTya Nnrml Nnrml = true;

val equal_SGNTy = {equal = equal_SGNTya} : sGNTy equal;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val plus_integer = {plus = (fn a => fn b => IntInf.+ (a, b))} : IntInf.int plus;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val semigroup_add_integer = {plus_semigroup_add = plus_integer} :
  IntInf.int semigroup_add;

val numeral_integer =
  {one_numeral = one_integer, semigroup_add_numeral = semigroup_add_integer} :
  IntInf.int numeral;

val times_integer = {times = (fn a => fn b => IntInf.* (a, b))} :
  IntInf.int times;

val power_integer = {one_power = one_integer, times_power = times_integer} :
  IntInf.int power;

val ab_semigroup_add_integer =
  {semigroup_add_ab_semigroup_add = semigroup_add_integer} :
  IntInf.int ab_semigroup_add;

val semigroup_mult_integer = {times_semigroup_mult = times_integer} :
  IntInf.int semigroup_mult;

val semiring_integer =
  {ab_semigroup_add_semiring = ab_semigroup_add_integer,
    semigroup_mult_semiring = semigroup_mult_integer}
  : IntInf.int semiring;

val mult_zero_integer =
  {times_mult_zero = times_integer, zero_mult_zero = zero_integer} :
  IntInf.int mult_zero;

val monoid_add_integer =
  {semigroup_add_monoid_add = semigroup_add_integer,
    zero_monoid_add = zero_integer}
  : IntInf.int monoid_add;

val comm_monoid_add_integer =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_integer,
    monoid_add_comm_monoid_add = monoid_add_integer}
  : IntInf.int comm_monoid_add;

val semiring_0_integer =
  {comm_monoid_add_semiring_0 = comm_monoid_add_integer,
    mult_zero_semiring_0 = mult_zero_integer,
    semiring_semiring_0 = semiring_integer}
  : IntInf.int semiring_0;

val monoid_mult_integer =
  {semigroup_mult_monoid_mult = semigroup_mult_integer,
    power_monoid_mult = power_integer}
  : IntInf.int monoid_mult;

val semiring_numeral_integer =
  {monoid_mult_semiring_numeral = monoid_mult_integer,
    numeral_semiring_numeral = numeral_integer,
    semiring_semiring_numeral = semiring_integer}
  : IntInf.int semiring_numeral;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

val semiring_1_integer =
  {semiring_numeral_semiring_1 = semiring_numeral_integer,
    semiring_0_semiring_1 = semiring_0_integer,
    zero_neq_one_semiring_1 = zero_neq_one_integer}
  : IntInf.int semiring_1;

datatype nat = Zero_nat | Suc of nat;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype exp = Expid of char list | Expapp of exp * exp list | Exppar of exp |
  Num of int | PlusExp of exp * exp | MinusExp of exp * exp | GtExp of exp * exp
  | GtEqExp of exp * exp | LtExp of exp * exp | LtEqExp of exp * exp |
  Srange of exp * exp | Ext of exp list | Prfx of exp * exp | STOP | SKIP |
  Let_within of decl list * exp | If_then_else of exp * exp * exp |
  SeqComp of exp * exp | Interleave of exp * exp |
  Parallel of exp * exp * exp list | IntChoice of exp * exp |
  ExtChoice of exp * exp | RepExtChoice of stmt * exp
and decl = Channel of (char list) list | Eqdecl of exp * exp |
  Assert of exp * exp
and stmt = Stmt of char list * exp;

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype aExp = AExpid of char list | AExpset of aExp | AExpTrcl of aExp |
  AExpno of aExp | AExpthis | AExpIdn | AExpnone | AExpeq of aExp * aExp |
  AExpneq of aExp * aExp | AExpDot of aExp * aExp | AExpPlus of aExp * aExp |
  AExpAnd of aExp * aExp;

datatype mult = Mlone | Mone | Msome;

datatype declExp = Dset of mult option * aExp;

datatype decla = Dc of (char list) list * declExp;

datatype sigTy = Sabstract | Snormal;

datatype cSPSpec = Csp of decl list;

datatype sigDecl =
  Sig of
    sigTy * mult option * (char list) list * (char list) option * decla list *
      aExp list;

datatype factDecl = Fact of char list * aExp list;

datatype checkDecl = Check of char list * nat;

datatype assertDecl = Asserta of char list * aExp list;

datatype alloyParagraph = Psig of sigDecl | Pfact of factDecl |
  Passert of assertDecl | Pcheck of checkDecl;

datatype alloyModule = Amodule of char list * alloyParagraph list;

datatype 'a gr_ext =
  Gr_ext of
    (char list) set * (char list) set * (char list -> (char list) option) *
      (char list -> (char list) option) * 'a;

datatype multUVal = Val of nat | Many;

datatype multVal = Rm of nat * multUVal | Sm of multUVal;

datatype 'a sGr_ext =
  SGr_ext of
    (char list -> sGNTy option) * (char list -> sGETy option) *
      (char list -> multVal option) * (char list -> multVal option) * 'a;

datatype 'a fr_ext =
  Fr_ext of unit sGr_ext gr_ext * (char list -> (char list) option) * 'a;

datatype gFGEdgeTy = Eimp | Econti;

datatype 'a gr_ls_ext =
  Gr_ls_ext of
    (char list) list * (char list) list * (char list * char list) list *
      (char list * char list) list * 'a;

datatype 'a sGr_ls_ext =
  SGr_ls_ext of
    (char list * sGNTy) list * (char list * sGETy) list *
      (char list * multVal) list * (char list * multVal) list * 'a;

datatype 'a fr_ls_ext =
  Fr_ls_ext of unit sGr_ls_ext gr_ls_ext * (char list * char list) list * 'a;

datatype 'a morph_ext =
  Morph_ext of
    (char list -> (char list) option) * (char list -> (char list) option) * 'a;

datatype 'a tFr_ls_ext =
  TFr_ls_ext of unit fr_ls_ext * (char list * sGETy) list * 'a;

datatype 'a gFGr_ls_ext = GFGr_ls_ext of (char list * gFGEdgeTy) list * 'a;

datatype 'a mdl_ls_ext =
  Mdl_ls_ext of
    unit gFGr_ls_ext gr_ls_ext * (char list * unit fr_ls_ext) list * 'a;

datatype 'a morphL_ext =
  MorphL_ext of
    (char list * char list) list * (char list * char list) list * 'a;

datatype 'a tyMdl_ls_ext =
  TyMdl_ls_ext of
    unit gFGr_ls_ext gr_ls_ext * (char list * unit tFr_ls_ext) list * 'a;

datatype 'a mdlTy_ls_ext =
  MdlTy_ls_ext of unit tyMdl_ls_ext * unit mdl_ls_ext * unit morphL_ext * 'a;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

val one_nat : nat = Suc Zero_nat;

fun nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nat m m)
                          end
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nat m m
                          end
  | nat_of_num One = one_nat;

fun nat (Pos k) = nat_of_num k
  | nat Zero_int = Zero_nat
  | nat (Neg k) = Zero_nat;

fun less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false
and less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true;

fun upt i j = (if less_nat i j then i :: upt (Suc i) j else []);

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun null [] = true
  | null (x :: xs) = false;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun remove A_ x (Coset xs) = Coset (inserta A_ x xs)
  | remove A_ x (Set xs) = Set (removeAll A_ x xs);

fun hd (x21 :: x22) = x21;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun map_comp f g = (fn k => (case g k of NONE => NONE | SOME a => f a));

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun less_num (Bit1 m) (Bit0 n) = less_num m n
  | less_num (Bit1 m) (Bit1 n) = less_num m n
  | less_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_num (Bit0 m) (Bit0 n) = less_num m n
  | less_num One (Bit1 n) = true
  | less_num One (Bit0 n) = true
  | less_num m One = false
and less_eq_num (Bit1 m) (Bit0 n) = less_num m n
  | less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n
  | less_eq_num (Bit1 m) One = false
  | less_eq_num (Bit0 m) One = false
  | less_eq_num One n = true;

fun less_int (Neg k) (Neg l) = less_num l k
  | less_int (Neg k) (Pos l) = true
  | less_int (Neg k) Zero_int = true
  | less_int (Pos k) (Neg l) = false
  | less_int (Pos k) (Pos l) = less_num k l
  | less_int (Pos k) Zero_int = false
  | less_int Zero_int (Neg l) = false
  | less_int Zero_int (Pos l) = true
  | less_int Zero_int Zero_int = false;

fun fst (x1, x2) = x1;

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

fun divmod_nat m n =
  (if equal_nat n Zero_nat orelse less_nat m n then (Zero_nat, m)
    else let
           val a = divmod_nat (minus_nat m n) n;
           val (q, aa) = a;
         in
           (Suc q, aa)
         end);

fun divide_nat m n = fst (divmod_nat m n);

fun snd (x1, x2) = x2;

fun mod_nat m n = snd (divmod_nat m n);

fun of_nat_aux A_ inc Zero_nat i = i
  | of_nat_aux A_ inc (Suc n) i = of_nat_aux A_ inc n (inc i);

fun of_nat A_ n =
  of_nat_aux A_
    (fn i =>
      plus ((plus_semigroup_add o semigroup_add_numeral o
              numeral_semiring_numeral o semiring_numeral_semiring_1)
             A_)
        i (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1)
                 A_)))
    n (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
              A_));

fun integer_of_nat x = of_nat semiring_1_integer x;

fun char_of_nat x = ((Char.chr o IntInf.toInt) o integer_of_nat) x;

fun str_nat n =
  (if less_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One))))
    then [char_of_nat
            (plus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))) n)]
    else str_nat (divide_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One))))) @
           [char_of_nat
              (plus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
                (mod_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One))))))]);

fun str_int i =
  (if less_int i Zero_int then [#"-"] @ str_nat (nat (uminus_int i))
    else str_nat (nat i));

fun is_none (SOME x) = false
  | is_none NONE = true;

fun gen_length n (x :: xs) = gen_length (Suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun size_list x = gen_length Zero_nat x;

fun enum xs = zip xs (upt Zero_nat (size_list xs));

fun tgt (Gr_ext (ns, es, src, tgt, more)) = tgt;

fun src (Gr_ext (ns, es, src, tgt, more)) = src;

fun es (Gr_ext (ns, es, src, tgt, more)) = es;

fun esId g =
  filter (fn e => equal_optiona (equal_list equal_char) (src g e) (tgt g e))
    (es g);

fun esG (Gr_ls_ext (nsG, esG, srcG, tgtG, more)) = esG;

fun toSetExt l = Ext (map Expid l);

fun toCSP_of_PDG_edges pdg =
  let
    val es = esG pdg;
  in
    [Channel es, Eqdecl (Expid [#"e", #"d", #"g", #"e", #"s"], toSetExt es)]
  end;

fun the (SOME x2) = x2;

fun buildCSPExpOfEdge e i =
  Prfx (Expid e,
         (if is_none i then SKIP
           else Expapp
                  (Expid [#"P"],
                    [Num (plus_inta (of_nat semiring_1_int (the i))
                           (Pos One))])));

fun incidentEsSrc_ls_0 [] gl v = []
  | incidentEsSrc_ls_0 (e :: el) gl v =
    let
      val el2 = incidentEsSrc_ls_0 el gl v;
    in
      (if equal_optiona (equal_list equal_char) (src gl e) (SOME v)
        then e :: el2 else el2)
    end;

fun tgtG (Gr_ls_ext (nsG, esG, srcG, tgtG, more)) = tgtG;

fun srcG (Gr_ls_ext (nsG, esG, srcG, tgtG, more)) = srcG;

fun nsG (Gr_ls_ext (nsG, esG, srcG, tgtG, more)) = nsG;

fun toGr gl =
  Gr_ext
    (Set (nsG gl), Set (esG gl), map_of (equal_list equal_char) (srcG gl),
      map_of (equal_list equal_char) (tgtG gl), ());

fun incidentEsSrc_ls g v = incidentEsSrc_ls_0 (esG g) (toGr g) v;

fun nonOutNodes0 g [] = []
  | nonOutNodes0 g (v :: vs) =
    (if null (incidentEsSrc_ls g v) then nonOutNodes0 g vs
      else v :: nonOutNodes0 g vs);

fun nonOutNodes g = nonOutNodes0 g (nsG g);

fun buildCSPExpOfEdges [] pdg = SKIP
  | buildCSPExpOfEdges (e :: es) pdg =
    let
      val f_idx_tgt =
        map_comp (map_of (equal_list equal_char) (enum (nonOutNodes pdg)))
          (map_of (equal_list equal_char) (tgtG pdg));
      val exp = buildCSPExpOfEdge e (f_idx_tgt e);
    in
      (if null es then exp else ExtChoice (exp, buildCSPExpOfEdges es pdg))
    end;

fun toCSP_of_PDG_Graph_NPrdecl vp pdg =
  let
    val es_inc_src = incidentEsSrc_ls pdg (fst vp);
  in
    Eqdecl
      (Expapp
         (Expid [#"P"],
           [Num (of_nat semiring_1_int (plus_nat (snd vp) one_nat))]),
        buildCSPExpOfEdges es_inc_src pdg)
  end;

fun toCSP_of_PDG_Graph_decls [] pdg = []
  | toCSP_of_PDG_Graph_decls (v :: vs) pdg =
    toCSP_of_PDG_Graph_NPrdecl v pdg :: toCSP_of_PDG_Graph_decls vs pdg;

fun toCSP_of_PDG_Graph_def pdg =
  let
    val ns = enum (nonOutNodes pdg);
  in
    Let_within
      (toCSP_of_PDG_Graph_decls ns pdg,
        RepExtChoice
          (Stmt ([#"i"],
                  Srange
                    (Num (Pos One),
                      Num (of_nat semiring_1_int (size_list ns)))),
            Expapp (Expid [#"P"], [Expid [#"i"]])))
  end;

fun toCSP_of_PDG pdg =
  Eqdecl
    (Expid [#"P", #"o", #"r", #"t", #"D", #"e", #"p", #"e", #"n", #"d", #"a",
             #"n", #"c", #"y", #"G", #"r", #"a", #"p", #"h"],
      toCSP_of_PDG_Graph_def pdg);

fun limited_Pr n =
  Eqdecl
    (Expid [#"L", #"i", #"m", #"i", #"t", #"e", #"d"],
      Let_within
        ([Eqdecl
            (Expapp
               (Expid [#"L", #"i", #"m", #"i", #"t", #"e", #"d", #"0"],
                 [Expid [#"E"], Expid [#"n"]]),
              If_then_else
                (GtExp (Expid [#"n"], Num Zero_int),
                  RepExtChoice
                    (Stmt ([#"e"], Expid [#"E"]),
                      Prfx (Expid [#"e"],
                             Exppar
                               (IntChoice
                                 (Expapp
                                    (Expid [#"L", #"i", #"m", #"i", #"t", #"e",
     #"d", #"0"],
                                      [Expid [#"E"],
MinusExp (Expid [#"n"], Num (Pos One))]),
                                   SKIP)))),
                  STOP))],
          Expapp
            (Expid [#"L", #"i", #"m", #"i", #"t", #"e", #"d", #"0"],
              [Expid [#"e", #"d", #"g", #"e", #"s"],
                Num (of_nat semiring_1_int n)])));

fun toCSP pdg =
  Csp (toCSP_of_PDG_edges pdg @
        [limited_Pr (size_list (esG pdg)), toCSP_of_PDG pdg,
          Assert
            (Expid [#"L", #"i", #"m", #"i", #"t", #"e", #"d"],
              Expid [#"P", #"o", #"r", #"t", #"D", #"e", #"p", #"e", #"n", #"d",
                      #"a", #"n", #"c", #"y", #"G", #"r", #"a", #"p", #"h"])]);

fun sg (Fr_ext (sg, tr, more)) = sg;

fun tr (Fr_ext (sg, tr, more)) = tr;

fun nty (Gr_ext (ns, es, src, tgt, SGr_ext (nty, ety, srcm, tgtm, more))) = nty;

fun ety (Gr_ext (ns, es, src, tgt, SGr_ext (nty, ety, srcm, tgtm, more))) = ety;

fun is_RP e f =
  member (equal_list equal_char) e (es (sg f)) andalso
    (equal_optiona equal_SGETy (ety (sg f) e) (SOME Eref) andalso
      equal_optiona equal_SGNTy (nty (sg f) (the (src (sg f) e))) (SOME Nprxy));

fun tr_ls (Fr_ls_ext (sg_ls, tr_ls, more)) = tr_ls;

fun sg_ls (Fr_ls_ext (sg_ls, tr_ls, more)) = sg_ls;

fun tgtmG
  (Gr_ls_ext
    (nsG, esG, srcG, tgtG, SGr_ls_ext (ntyG, etyG, srcmG, tgtmG, more)))
  = tgtmG;

fun srcmG
  (Gr_ls_ext
    (nsG, esG, srcG, tgtG, SGr_ls_ext (ntyG, etyG, srcmG, tgtmG, more)))
  = srcmG;

fun ntyG
  (Gr_ls_ext
    (nsG, esG, srcG, tgtG, SGr_ls_ext (ntyG, etyG, srcmG, tgtmG, more)))
  = ntyG;

fun etyG
  (Gr_ls_ext
    (nsG, esG, srcG, tgtG, SGr_ls_ext (ntyG, etyG, srcmG, tgtmG, more)))
  = etyG;

fun toSGr sgl =
  Gr_ext
    (Set (nsG sgl), Set (esG sgl), map_of (equal_list equal_char) (srcG sgl),
      map_of (equal_list equal_char) (tgtG sgl),
      SGr_ext
        (map_of (equal_list equal_char) (ntyG sgl),
          map_of (equal_list equal_char) (etyG sgl),
          map_of (equal_list equal_char) (srcmG sgl),
          map_of (equal_list equal_char) (tgtmG sgl), ()));

fun toFr fl =
  Fr_ext (toSGr (sg_ls fl), map_of (equal_list equal_char) (tr_ls fl), ());

val emptyGL : unit gr_ls_ext = Gr_ls_ext ([], [], [], [], ());

fun wrConstraintOfEgdes pdg [] = AExpnone
  | wrConstraintOfEgdes pdg (e :: es) =
    (if null es then AExpid (the (tgt (toGr pdg) e))
      else AExpPlus
             (AExpid (the (tgt (toGr pdg) e)), wrConstraintOfEgdes pdg es));

fun wrConstraintOfNode pdg v =
  let
    val es_fr_v = incidentEsSrc_ls pdg v;
  in
    (if null es_fr_v then AExpno (AExpDot (AExpid v, AExpid [#"t", #"g", #"t"]))
      else AExpeq
             (AExpDot (AExpid v, AExpid [#"t", #"g", #"t"]),
               wrConstraintOfEgdes pdg es_fr_v))
  end;

fun wrConstraintsOfNodes pdg vs = map (wrConstraintOfNode pdg) vs;

fun toAlloyFactOfPDGPorts pdg = Fact ([], wrConstraintsOfNodes pdg (nsG pdg));

fun toAlloySigOfPDGPorts pdg =
  Sig (Snormal, SOME Mone, nsG pdg, SOME [#"P", #"o", #"r", #"t"], [], []);

fun toAlloyCheck pdg =
  Check ([#"A", #"c", #"y", #"c", #"l", #"i", #"c", #"T", #"g", #"t"],
          size_list (nsG pdg));

fun toAlloy pdg =
  Amodule
    ([#"a", #"l", #"g", #"e", #"b", #"r", #"a", #"i", #"c", #"L", #"o", #"o",
       #"p", #"C", #"h", #"e", #"c", #"k"],
      [Psig (Sig (Sabstract, NONE, [[#"P", #"o", #"r", #"t"]], NONE,
                   [Dc ([[#"t", #"g", #"t"]],
                         Dset (NONE,
                                AExpset (AExpid [#"P", #"o", #"r", #"t"])))],
                   [AExpneq (AExpid [#"t", #"g", #"t"], AExpthis)])),
        Psig (toAlloySigOfPDGPorts pdg), Pfact (toAlloyFactOfPDGPorts pdg),
        Passert
          (Asserta
            ([#"A", #"c", #"y", #"c", #"l", #"i", #"c", #"T", #"g", #"t"],
              [AExpno
                 (AExpAnd (AExpTrcl (AExpid [#"t", #"g", #"t"]), AExpIdn))])),
        Pcheck (toAlloyCheck pdg)]);

fun consUSG sGL1 sGL2 =
  Gr_ls_ext
    (nsG sGL1 @ nsG sGL2, esG sGL1 @ esG sGL2, srcG sGL2 @ srcG sGL1,
      tgtG sGL2 @ tgtG sGL1,
      SGr_ls_ext
        (ntyG sGL2 @ ntyG sGL1, etyG sGL2 @ etyG sGL1, srcmG sGL2 @ srcmG sGL1,
          tgtmG sGL2 @ tgtmG sGL1, ()));

fun consUF fL1 fL2 =
  Fr_ls_ext (consUSG (sg_ls fL1) (sg_ls fL2), tr_ls fL2 @ tr_ls fL1, ());

val emptySGL : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext ([], [], [], [], SGr_ls_ext ([], [], [], [], ()));

val emptyFrL : unit fr_ls_ext = Fr_ls_ext (emptySGL, [], ());

fun consUFs [] = emptyFrL
  | consUFs (fl :: fLs) = consUF fl (consUFs fLs);

fun minus_set A_ a (Coset xs) = Set (filtera (fn x => member A_ x a) xs)
  | minus_set A_ a (Set xs) = fold (remove A_) xs a;

fun consInhE sg e =
  (if member (equal_list equal_char) e
        (minus_set (equal_list equal_char) (es sg) (esId sg)) andalso
        equal_optiona equal_SGETy (ety sg e) (SOME Einh)
    then [(the (src sg e), the (tgt sg e))] else []);

fun consInh0 sg [] = []
  | consInh0 sg (e :: es) = consInhE sg e @ consInh0 sg es;

fun consInh sg = consInh0 (toSGr sg) (esG sg);

val sG_F_CD : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
       [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e",
         #"n", #"t", #"5"],
       [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e", #"2"],
       [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"],
       [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s", #"D",
         #"i", #"a", #"g", #"r", #"a", #"m"],
       [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"],
       [#"P", #"o", #"r", #"t"],
       [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n", #"c",
         #"e"]],
      [[#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"n", #"n", #"e", #"c", #"t",
         #"i", #"o", #"n", #"s", #"D", #"i", #"a", #"g", #"r", #"a", #"m"],
        [#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k", #"I", #"n",
          #"s", #"t", #"a", #"n", #"c", #"e"],
        [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"],
        [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r",
          #"s"],
        [#"E", #"C", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"_", #"f", #"l", #"o", #"w", #"T", #"y", #"p", #"e"],
        [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"],
        [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"],
        [#"E", #"B", #"I", #"t", #"y", #"p", #"e"],
        [#"E", #"B", #"I", #"I", #"n", #"s", #"i", #"d", #"e"],
        [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"5"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p",
          #"e", #"2"],
        [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t",
          #"2"]],
      [([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"n", #"n", #"e", #"c", #"t",
          #"i", #"o", #"n", #"s", #"D", #"i", #"a", #"g", #"r", #"a", #"m"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
           #"D", #"i", #"a", #"g", #"r", #"a", #"m"]),
        ([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k", #"I",
           #"n", #"s", #"t", #"a", #"n", #"c", #"e"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
            #"D", #"i", #"a", #"g", #"r", #"a", #"m"]),
        ([#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
           #"r", #"s"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
            #"D", #"i", #"a", #"g", #"r", #"a", #"m"]),
        ([#"E", #"C", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
        ([#"E", #"C", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
        ([#"E", #"C", #"_", #"f", #"l", #"o", #"w", #"T", #"y", #"p", #"e"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
        ([#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"],
          [#"P", #"o", #"r", #"t"]),
        ([#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"B", #"I", #"t", #"y", #"p", #"e"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"B", #"I", #"I", #"n", #"s", #"i", #"d", #"e"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"5"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"5"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e", #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e",
            #"2"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t", #"2"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"])],
      [([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"n", #"n", #"e", #"c", #"t",
          #"i", #"o", #"n", #"s", #"D", #"i", #"a", #"g", #"r", #"a", #"m"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t", #"5"]),
        ([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k", #"I",
           #"n", #"s", #"t", #"a", #"n", #"c", #"e"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"5"]),
        ([#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
           #"r", #"s"],
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
        ([#"E", #"C", #"_", #"s", #"r", #"c"], [#"P", #"o", #"r", #"t"]),
        ([#"E", #"C", #"_", #"t", #"g", #"t"], [#"P", #"o", #"r", #"t"]),
        ([#"E", #"C", #"_", #"f", #"l", #"o", #"w", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e",
            #"2"]),
        ([#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
        ([#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"],
          [#"P", #"o", #"r", #"t"]),
        ([#"E", #"B", #"I", #"t", #"y", #"p", #"e"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"B", #"I", #"I", #"n", #"s", #"i", #"d", #"e"],
          [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
            #"c", #"e"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"5"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"5"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e", #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e",
            #"2"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t", #"2"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"])],
      SGr_ls_ext
        ([([#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"], Nprxy),
           ([#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
              #"e", #"n", #"t", #"5"],
             Nprxy),
           ([#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"],
             Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e",
              #"2"],
             Nprxy),
           ([#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
              #"D", #"i", #"a", #"g", #"r", #"a", #"m"],
             Nnrml),
           ([#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"], Nnrml),
           ([#"P", #"o", #"r", #"t"], Nnrml),
           ([#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
              #"c", #"e"],
             Nnrml)],
          [([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"n", #"n", #"e", #"c",
              #"t", #"i", #"o", #"n", #"s", #"D", #"i", #"a", #"g", #"r", #"a",
              #"m"],
             Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k", #"I",
               #"n", #"s", #"t", #"a", #"n", #"c", #"e"],
              Einh),
            ([#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"], Ecompuni),
            ([#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
               #"r", #"s"],
              Ecompuni),
            ([#"E", #"C", #"_", #"s", #"r", #"c"], Ereluni),
            ([#"E", #"C", #"_", #"t", #"g", #"t"], Ereluni),
            ([#"E", #"C", #"_", #"f", #"l", #"o", #"w", #"T", #"y", #"p", #"e"],
              Ereluni),
            ([#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"], Ereluni),
            ([#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"], Ecompuni),
            ([#"E", #"B", #"I", #"t", #"y", #"p", #"e"], Ereluni),
            ([#"E", #"B", #"I", #"I", #"n", #"s", #"i", #"d", #"e"], Ecompuni),
            ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
               #"e", #"m", #"e", #"n", #"t", #"5"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
               #"p", #"e", #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
               #"t", #"2"],
              Eref)],
          [], [([#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"],
                 Sm Many),
                ([#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t",
                   #"o", #"r", #"s"],
                  Sm Many),
                ([#"E", #"C", #"_", #"s", #"r", #"c"], Sm (Val one_nat)),
                ([#"E", #"C", #"_", #"t", #"g", #"t"], Sm (Val one_nat)),
                ([#"E", #"C", #"_", #"f", #"l", #"o", #"w", #"T", #"y", #"p",
                   #"e"],
                  Sm (Val one_nat)),
                ([#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"],
                  Sm (Val one_nat)),
                ([#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"], Sm Many),
                ([#"E", #"B", #"I", #"t", #"y", #"p", #"e"], Sm (Val one_nat)),
                ([#"E", #"B", #"I", #"I", #"n", #"s", #"i", #"d", #"e"],
                  Sm Many)],
          ()));

val f_CD : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_CD,
      [([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"],
         [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"5"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t", #"2"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e", #"2"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"])],
      ());

fun consRefsE f e =
  (if is_RP e f then [(the (src (sg f) e), the (tr f e))] else []);

fun consRefs0 f [] = []
  | consRefs0 f (e :: es) = consRefsE f e @ consRefs0 f es;

fun consRefs fl = consRefs0 (toFr fl) (esG (sg_ls fl));

fun consReps fl = let
                    val lrefs = consRefs fl;
                  in
                    lrefs @ zip (map snd lrefs) (map fst lrefs)
                  end;

fun consInhF fl = consInh (sg_ls fl) @ consReps fl;

val sG_F_ASD : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
       [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e",
         #"n", #"t", #"4"],
       [#"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o",
         #"n"],
       [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"],
       [#"A", #"S", #"D"]],
      [[#"E", #"I", #"S", #"u", #"p", #"A", #"S", #"D"],
        [#"E", #"b", #"l", #"o", #"c", #"k", #"s"],
        [#"E", #"c", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n",
          #"s"],
        [#"E", #"t", #"y", #"p", #"e", #"s"],
        [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"4"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t",
          #"i", #"o", #"n"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p",
          #"e"]],
      [([#"E", #"I", #"S", #"u", #"p", #"A", #"S", #"D"], [#"A", #"S", #"D"]),
        ([#"E", #"b", #"l", #"o", #"c", #"k", #"s"], [#"A", #"S", #"D"]),
        ([#"E", #"c", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o",
           #"n", #"s"],
          [#"A", #"S", #"D"]),
        ([#"E", #"t", #"y", #"p", #"e", #"s"], [#"A", #"S", #"D"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"4"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"4"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i",
           #"t", #"i", #"o", #"n"],
          [#"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i",
            #"o", #"n"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"])],
      [([#"E", #"I", #"S", #"u", #"p", #"A", #"S", #"D"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t", #"4"]),
        ([#"E", #"b", #"l", #"o", #"c", #"k", #"s"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"]),
        ([#"E", #"c", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o",
           #"n", #"s"],
          [#"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i",
            #"o", #"n"]),
        ([#"E", #"t", #"y", #"p", #"e", #"s"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"4"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"4"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i",
           #"t", #"i", #"o", #"n"],
          [#"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i",
            #"o", #"n"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"])],
      SGr_ls_ext
        ([([#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"], Nprxy),
           ([#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
              #"e", #"n", #"t", #"4"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i",
              #"o", #"n"],
             Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"],
             Nprxy),
           ([#"A", #"S", #"D"], Nnrml)],
          [([#"E", #"I", #"S", #"u", #"p", #"A", #"S", #"D"], Einh),
            ([#"E", #"b", #"l", #"o", #"c", #"k", #"s"], Ecompuni),
            ([#"E", #"c", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o",
               #"n", #"s"],
              Ecompuni),
            ([#"E", #"t", #"y", #"p", #"e", #"s"], Ecompuni),
            ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
               #"e", #"m", #"e", #"n", #"t", #"4"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i",
               #"t", #"i", #"o", #"n"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
               #"p", #"e"],
              Eref)],
          [], [([#"E", #"b", #"l", #"o", #"c", #"k", #"s"], Sm Many),
                ([#"E", #"c", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i",
                   #"o", #"n", #"s"],
                  Sm Many),
                ([#"E", #"t", #"y", #"p", #"e", #"s"], Sm Many)],
          ()));

val f_ASD : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_ASD,
      [([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"2"],
         [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"4"],
          [#"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e", #"n",
            #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"m", #"p", #"o", #"s", #"i",
           #"t", #"i", #"o", #"n"],
          [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
           #"p", #"e"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"])],
      ());

val tF_CD : unit tFr_ls_ext = TFr_ls_ext (f_CD, [], ());

fun relpow_impl succ un memb new have Zero_nat = un new have
  | relpow_impl succ un memb new have (Suc m) =
    (if null new then have
      else let
             val maybe = succ new;
             val havea = un new have;
             val newa = filtera (fn n => not (memb n havea)) maybe;
           in
             relpow_impl succ un memb newa havea m
           end);

fun rtrancl_impl gen_succ un memb emp rel =
  let
    val succ = gen_succ rel;
    val n = size_list rel;
  in
    (fn asa => relpow_impl succ un memb asa emp n)
  end;

fun rtrancl_list_impl A_ =
  rtrancl_impl
    (fn r => fn asa =>
      remdups A_
        (map_filter
          (fn x => (if let
                         val (a, _) = x;
                       in
                         membera A_ asa a
                       end
                     then SOME (snd x) else NONE))
          r))
    (fn xs => fn ys => filtera (fn x => not (membera A_ ys x)) xs @ ys)
    (fn x => fn xs => membera A_ xs x) [];

fun consClanF v fl =
  let
    val consInhFa = consInhF fl;
  in
    rtrancl_list_impl (equal_list equal_char)
      (zip (map snd consInhFa) (map fst consInhFa)) [v]
  end;

fun consUG gL1 gL2 =
  Gr_ls_ext
    (nsG gL1 @ nsG gL2, esG gL1 @ esG gL2, srcG gL2 @ srcG gL1,
      tgtG gL2 @ tgtG gL1, ());

val gFG_3WTs : unit gFGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s"],
       [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"]],
      [[#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
         #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
          #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"]],
      [([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
          #"A", #"S", #"D"],
         [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
           #"s"],
          [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
          [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"])],
      [([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
          #"A", #"S", #"D"],
         [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
           #"s"],
          [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
          [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"])],
      GFGr_ls_ext
        ([([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s",
             #"_", #"A", #"S", #"D"],
            Eimp),
           ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
              #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
             Eimp)],
          ()));

val sG_ASD_3WTs : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A", #"S",
        #"D"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S", #"y",
         #"s"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"1"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"2"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"3"],
       [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
         #"1"],
       [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
         #"2"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
         #"n", #"k"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
         #"n", #"k"],
       [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
       [#"V", #"a", #"l", #"v", #"e"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
       [#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
       [#"A", #"r", #"e", #"a"], [#"H", #"e", #"i", #"g", #"h", #"t"],
       [#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"i",
         #"n"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"o",
         #"u", #"t"],
       [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
       [#"V", #"a", #"l", #"v", #"e", #"_", #"w"],
       [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"v",
         #"1"]],
      [[#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
         #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
         #"s", #"S", #"y", #"s"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s",
          #"e", #"d"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e",
          #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e",
          #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
        [#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"i", #"n"],
        [#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"o", #"u", #"t"],
        [#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
        [#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
        [#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"v", #"1"],
        [#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
        [#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_", #"w",
          #"i", #"n"]],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
           #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"3"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"3"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"])],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
           #"y", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"A", #"r", #"e", #"a"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"H", #"e", #"i", #"g", #"h", #"t"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"v", #"1"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"])],
      SGr_ls_ext
        ([([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
             #"S", #"D"],
            Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
              #"y", #"s"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"1"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"2"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"3"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
              #"T", #"a", #"n", #"k"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
              #"T", #"a", #"n", #"k"],
             Nnrml),
           ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
              #"l", #"1"],
             Nnrml),
           ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
              #"l", #"2"],
             Nnrml),
           ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
             Nnrml),
           ([#"V", #"a", #"l", #"v", #"e"], Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"], Nnrml),
           ([#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"], Nnrml),
           ([#"A", #"r", #"e", #"a"], Nnrml),
           ([#"H", #"e", #"i", #"g", #"h", #"t"], Nnrml),
           ([#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
             Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
              #"i", #"n"],
             Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
              #"o", #"u", #"t"],
             Nnrml),
           ([#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"], Nnrml),
           ([#"V", #"a", #"l", #"v", #"e", #"_", #"w"], Nnrml),
           ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
              #"v", #"1"],
             Nnrml)],
          [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
              #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s"],
             Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"1"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"2"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
               #"e"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
               #"s", #"e", #"d"],
              Elnk),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
               #"e", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
               #"e", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
               #"_", #"w", #"i", #"n"],
              Elnk),
            ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
               #"_", #"w", #"o", #"u", #"t"],
              Elnk),
            ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"], Elnk),
            ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
               #"r", #"_", #"v", #"1"],
              Elnk),
            ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
               #"w", #"i", #"n"],
              Elnk)],
          [], [([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                  #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_",
                  #"s", #"r", #"c"],
                 Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_",
                   #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_",
                   #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a",
                   #"l", #"v", #"e", #"_", #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r",
                   #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r",
                   #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a",
                   #"l", #"v", #"e", #"_", #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g",
                   #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g",
                   #"t"],
                  Sm (Val (nat_of_num (Bit0 One))))],
          ()));

val f_ASD_3WTs : unit fr_ls_ext = Fr_ls_ext (sG_ASD_3WTs, [], ());

val sG_CD_3WTs : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e"],
       [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
         #"o", #"l", #"1"],
       [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
         #"o", #"l", #"2"],
       [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
       [#"C", #"D", #"_", #"3", #"W", #"T", #"s"],
       [#"W", #"T", #"S", #"y", #"s"], [#"V"], [#"W", #"T", #"1"],
       [#"W", #"T", #"2"], [#"W", #"T", #"3"], [#"C"], [#"T", #"C", #"1"],
       [#"T", #"C", #"2"], [#"v", #"1"], [#"v", #"2"], [#"w"],
       [#"w", #"i", #"n", #"1"], [#"w", #"o", #"u", #"t", #"1"],
       [#"w", #"i", #"n", #"2"], [#"w", #"o", #"u", #"t", #"2"],
       [#"w", #"i", #"n", #"3"], [#"w", #"o", #"u", #"t", #"3"],
       [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"],
       [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n", #"2"],
       [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n", #"3"],
       [#"C", #"_", #"v", #"1", #"_", #"v", #"2"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
       [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
         #"w", #"i", #"n"],
       [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
         #"w", #"o", #"u", #"t"],
       [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
         #"_", #"v", #"1"]],
      [[#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
        [#"E", #"C", #"D", #"_", #"V"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
        [#"E", #"C", #"D", #"_", #"C"],
        [#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
        [#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
          #"1"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_",
          #"w", #"i", #"n", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_",
          #"w", #"i", #"n", #"3"],
        [#"E", #"_", #"C", #"_", #"v", #"1"],
        [#"E", #"_", #"V", #"_", #"v", #"2"], [#"E", #"_", #"V", #"_", #"w"],
        [#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
        [#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
        [#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
        [#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
        [#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
        [#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
        [#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s", #"r",
          #"c"],
        [#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t", #"g",
          #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_", #"s",
          #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_", #"t",
          #"g", #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i",
          #"n", #"2", #"_", #"s", #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i",
          #"n", #"2", #"_", #"t", #"g", #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i",
          #"n", #"3", #"_", #"s", #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i",
          #"n", #"3", #"_", #"t", #"g", #"t"],
        [#"E", #"T", #"C", #"1", #"_", #"V"],
        [#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"],
        [#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"],
        [#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"],
        [#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
        [#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1"],
        [#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l",
          #"e", #"r"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
          #"2"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"_", #"w", #"i", #"n"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"_", #"w", #"o", #"u", #"t"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l",
          #"e", #"r", #"_", #"v", #"1"]],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"], [#"C"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"], [#"V"]),
        ([#"E", #"_", #"V", #"_", #"w"], [#"V"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"W", #"T", #"1"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"W", #"T", #"1"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"W", #"T", #"2"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"W", #"T", #"2"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"W", #"T", #"3"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"W", #"T", #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"T", #"C", #"1", #"_", #"V"], [#"T", #"C", #"1"]),
        ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], [#"T", #"C", #"1"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], [#"T", #"C", #"2"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], [#"T", #"C", #"2"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"], [#"v", #"1"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"], [#"v", #"2"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"], [#"w"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"3"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"])],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"], [#"V"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"], [#"W", #"T", #"1"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"], [#"W", #"T", #"2"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"], [#"W", #"T", #"3"]),
        ([#"E", #"C", #"D", #"_", #"C"], [#"C"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"], [#"T", #"C", #"1"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"], [#"T", #"C", #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"], [#"v", #"1"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"], [#"v", #"2"]),
        ([#"E", #"_", #"V", #"_", #"w"], [#"w"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"w", #"o", #"u", #"t", #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"v", #"1"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"w"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"T", #"C", #"1", #"_", #"V"], [#"V"]),
        ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], [#"W", #"T", #"1"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], [#"W", #"T", #"2"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], [#"W", #"T", #"3"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
          [#"T", #"C", #"1"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
          [#"T", #"C", #"2"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"], [#"C"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"])],
      SGr_ls_ext
        ([([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
            Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e"], Nprxy),
           ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
              #"r", #"o", #"l", #"1"],
             Nprxy),
           ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
              #"r", #"o", #"l", #"2"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
              #"r"],
             Nprxy),
           ([#"C", #"D", #"_", #"3", #"W", #"T", #"s"], Nnrml),
           ([#"W", #"T", #"S", #"y", #"s"], Nnrml), ([#"V"], Nnrml),
           ([#"W", #"T", #"1"], Nnrml), ([#"W", #"T", #"2"], Nnrml),
           ([#"W", #"T", #"3"], Nnrml), ([#"C"], Nnrml),
           ([#"T", #"C", #"1"], Nnrml), ([#"T", #"C", #"2"], Nnrml),
           ([#"v", #"1"], Nnrml), ([#"v", #"2"], Nnrml), ([#"w"], Nnrml),
           ([#"w", #"i", #"n", #"1"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"1"], Nnrml),
           ([#"w", #"i", #"n", #"2"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"2"], Nnrml),
           ([#"w", #"i", #"n", #"3"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"3"], Nnrml),
           ([#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"], Nnrml),
           ([#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
              #"2"],
             Nnrml),
           ([#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
              #"3"],
             Nnrml),
           ([#"C", #"_", #"v", #"1", #"_", #"v", #"2"], Nnrml),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
             Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"], Nprxy),
           ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
              #"_", #"w", #"i", #"n"],
             Nprxy),
           ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
              #"_", #"w", #"o", #"u", #"t"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
              #"r", #"_", #"v", #"1"],
             Nprxy)],
          [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"], Elnk),
            ([#"E", #"C", #"D", #"_", #"V"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"], Elnk),
            ([#"E", #"C", #"D", #"_", #"C"], Elnk),
            ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"], Elnk),
            ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"], Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
               #"1"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
               #"_", #"w", #"i", #"n", #"2"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
               #"_", #"w", #"i", #"n", #"3"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1"], Elnk),
            ([#"E", #"_", #"V", #"_", #"v", #"2"], Elnk),
            ([#"E", #"_", #"V", #"_", #"w"], Elnk),
            ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
               #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
               #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
               #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
               #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
               #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
               #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
               #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
               #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"T", #"C", #"1", #"_", #"V"], Elnk),
            ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], Elnk),
            ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], Elnk),
            ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
              Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
              Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"], Elnk),
            ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"], Eref),
            ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"1"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
               #"l", #"e", #"r"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
               #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k", #"_", #"w", #"i", #"n"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
               #"l", #"e", #"r", #"_", #"v", #"1"],
              Eref)],
          [], [], ()));

val f_CD_3WTs : unit fr_ls_ext =
  Fr_ls_ext
    (sG_CD_3WTs,
      [([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"v", #"1"])],
      ());

val mdl_3WTs : unit mdl_ls_ext =
  Mdl_ls_ext
    (gFG_3WTs,
      [([#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s"],
         f_ASD_3WTs),
        ([#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"], f_CD_3WTs)],
      ());

val tF_ASD : unit tFr_ls_ext = TFr_ls_ext (f_ASD, [], ());

val bot_set : 'a set = Set [];

fun consSrcStFE fl e =
  (if member (equal_option equal_SGETy) (ety (sg (toFr fl)) e)
        (insert (equal_option equal_SGETy) (SOME Ecompbi)
          (insert (equal_option equal_SGETy) (SOME Ecompuni)
            (insert (equal_option equal_SGETy) (SOME Erelbi)
              (insert (equal_option equal_SGETy) (SOME Ereluni)
                (insert (equal_option equal_SGETy) (SOME Elnk) bot_set)))))
    then map (fn a => (e, a)) (consClanF (the (src (sg (toFr fl)) e)) fl)
    else []);

fun consSrcStF0 fl [] = []
  | consSrcStF0 fl (e :: es) = consSrcStFE fl e @ consSrcStF0 fl es;

fun consSrcStF fl = consSrcStF0 fl (esG (sg_ls fl));

fun consTgtStFE fl e =
  (if member (equal_option equal_SGETy) (ety (sg (toFr fl)) e)
        (insert (equal_option equal_SGETy) (SOME Ecompbi)
          (insert (equal_option equal_SGETy) (SOME Ecompuni)
            (insert (equal_option equal_SGETy) (SOME Erelbi)
              (insert (equal_option equal_SGETy) (SOME Ereluni)
                (insert (equal_option equal_SGETy) (SOME Elnk) bot_set)))))
    then map (fn a => (e, a)) (consClanF (the (tgt (sg (toFr fl)) e)) fl)
    else []);

fun consTgtStF0 fl [] = []
  | consTgtStF0 fl (e :: es) = consTgtStFE fl e @ consTgtStF0 fl es;

fun consTgtStF fl = consTgtStF0 fl (esG (sg_ls fl));

fun fE (Morph_ext (fV, fE, more)) = fE;

fun fV (Morph_ext (fV, fE, more)) = fV;

fun fVL (MorphL_ext (fVL, fEL, more)) = fVL;

fun fEL (MorphL_ext (fVL, fEL, more)) = fEL;

fun consUGM mL1 mL2 = MorphL_ext (fVL mL2 @ fVL mL1, fEL mL2 @ fEL mL1, ());

fun toMorph ml =
  Morph_ext
    (map_of (equal_list equal_char) (fVL ml),
      map_of (equal_list equal_char) (fEL ml), ());

val sG_F_Comps : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"B", #"l", #"o", #"c", #"k"],
       [#"P", #"r", #"N", #"a", #"t"],
       [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"],
       [#"M", #"u", #"l", #"t"],
       [#"M", #"u", #"l", #"t", #"R", #"a", #"n", #"g", #"e"],
       [#"M", #"u", #"l", #"t", #"S", #"i", #"n", #"g", #"l", #"e"],
       [#"M", #"u", #"l", #"t", #"V", #"a", #"l"],
       [#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"N", #"u", #"m"],
       [#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"M", #"a", #"n", #"y"]],
      [[#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"S", #"i", #"n",
         #"g", #"l", #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"R", #"a", #"n",
          #"g", #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a", #"l",
          #"N", #"u", #"m"],
        [#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a", #"l",
          #"M", #"a", #"n", #"y"],
        [#"E", #"v", #"a", #"l"], [#"E", #"l", #"b"], [#"E", #"u", #"b"],
        [#"E", #"n"], [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"t"]],
      [([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"S", #"i", #"n",
          #"g", #"l", #"e"],
         [#"M", #"u", #"l", #"t", #"S", #"i", #"n", #"g", #"l", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"R", #"a",
           #"n", #"g", #"e"],
          [#"M", #"u", #"l", #"t", #"R", #"a", #"n", #"g", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
           #"l", #"N", #"u", #"m"],
          [#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"N", #"u", #"m"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
           #"l", #"M", #"a", #"n", #"y"],
          [#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"M", #"a", #"n", #"y"]),
        ([#"E", #"v", #"a", #"l"],
          [#"M", #"u", #"l", #"t", #"S", #"i", #"n", #"g", #"l", #"e"]),
        ([#"E", #"l", #"b"],
          [#"M", #"u", #"l", #"t", #"R", #"a", #"n", #"g", #"e"]),
        ([#"E", #"u", #"b"],
          [#"M", #"u", #"l", #"t", #"R", #"a", #"n", #"g", #"e"]),
        ([#"E", #"n"],
          [#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"N", #"u", #"m"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"t"],
          [#"P", #"r", #"N", #"a", #"t"])],
      [([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"S", #"i", #"n",
          #"g", #"l", #"e"],
         [#"M", #"u", #"l", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"R", #"a",
           #"n", #"g", #"e"],
          [#"M", #"u", #"l", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
           #"l", #"N", #"u", #"m"],
          [#"M", #"u", #"l", #"t", #"V", #"a", #"l"]),
        ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
           #"l", #"M", #"a", #"n", #"y"],
          [#"M", #"u", #"l", #"t", #"V", #"a", #"l"]),
        ([#"E", #"v", #"a", #"l"], [#"M", #"u", #"l", #"t", #"V", #"a", #"l"]),
        ([#"E", #"l", #"b"], [#"P", #"r", #"N", #"a", #"t"]),
        ([#"E", #"u", #"b"], [#"M", #"u", #"l", #"t", #"V", #"a", #"l"]),
        ([#"E", #"n"], [#"P", #"r", #"N", #"a", #"t"]),
        ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k"],
          [#"P", #"r", #"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"t"],
          [#"P", #"r", #"N", #"a", #"t"])],
      SGr_ls_ext
        ([([#"P", #"r", #"B", #"l", #"o", #"c", #"k"], Nprxy),
           ([#"P", #"r", #"N", #"a", #"t"], Nprxy),
           ([#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"],
             Nnrml),
           ([#"M", #"u", #"l", #"t"], Nnrml),
           ([#"M", #"u", #"l", #"t", #"R", #"a", #"n", #"g", #"e"], Nnrml),
           ([#"M", #"u", #"l", #"t", #"S", #"i", #"n", #"g", #"l", #"e"],
             Nnrml),
           ([#"M", #"u", #"l", #"t", #"V", #"a", #"l"], Nnrml),
           ([#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"N", #"u", #"m"],
             Nnrml),
           ([#"M", #"u", #"l", #"t", #"V", #"a", #"l", #"M", #"a", #"n", #"y"],
             Nnrml)],
          [([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"S", #"i",
              #"n", #"g", #"l", #"e"],
             Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"R", #"a",
               #"n", #"g", #"e"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
               #"l", #"N", #"u", #"m"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"M", #"u", #"l", #"t", #"V", #"a",
               #"l", #"M", #"a", #"n", #"y"],
              Einh),
            ([#"E", #"v", #"a", #"l"], Ereluni), ([#"E", #"l", #"b"], Ereluni),
            ([#"E", #"u", #"b"], Ereluni), ([#"E", #"n"], Ereluni),
            ([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k"], Eref),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"t"], Eref)],
          [], [([#"E", #"v", #"a", #"l"], Sm (Val one_nat)),
                ([#"E", #"l", #"b"], Sm (Val one_nat)),
                ([#"E", #"u", #"b"], Sm (Val one_nat)),
                ([#"E", #"n"], Sm (Val one_nat))],
          ()));

val f_Comps : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_Comps,
      [([#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k"],
         [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"t"], [#"N", #"a", #"t"])],
      ());

val sG_F_Props : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e",
        #"n", #"t"],
       [#"P", #"r", #"T", #"y", #"p", #"e"],
       [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"],
       [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"],
       [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"],
       [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"],
       [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #"K", #"i", #"n", #"d"],
       [#"D", #"i", #"r", #"e", #"c", #"t", #"i", #"o", #"n"]],
      [[#"E", #"I", #"S", #"u", #"p", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
         #"y"],
        [#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
          #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
          #"t"],
        [#"E", #"P", #"r", #"o", #"p", #"I", #"n", #"i", #"t"],
        [#"E", #"P", #"r", #"o", #"p", #"T", #"y", #"p", #"e"],
        [#"E", #"V", #"a", #"r", #"K", #"i", #"n", #"d"],
        [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"i", #"r",
          #"e", #"c", #"t", #"i", #"o", #"n"],
        [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e", #"p",
          #"e", #"n", #"d", #"s"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t"],
        [#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e"],
        [#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"]],
      [([#"E", #"I", #"S", #"u", #"p", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
          #"y"],
         [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"r", #"i", #"a", #"b",
           #"l", #"e"],
          [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"F", #"l", #"o", #"w", #"P", #"o",
           #"r", #"t"],
          [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"P", #"r", #"o", #"p", #"I", #"n", #"i", #"t"],
          [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"P", #"r", #"o", #"p", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"V", #"a", #"r", #"K", #"i", #"n", #"d"],
          [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"]),
        ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"i",
           #"r", #"e", #"c", #"t", #"i", #"o", #"n"],
          [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
           #"p", #"e", #"n", #"d", #"s"],
          [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"])],
      [([#"E", #"I", #"S", #"u", #"p", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
          #"y"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"r", #"i", #"a", #"b",
           #"l", #"e"],
          [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"I", #"S", #"u", #"p", #"F", #"l", #"o", #"w", #"P", #"o",
           #"r", #"t"],
          [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"P", #"r", #"o", #"p", #"I", #"n", #"i", #"t"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"]),
        ([#"E", #"P", #"r", #"o", #"p", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"T", #"y", #"p", #"e"]),
        ([#"E", #"V", #"a", #"r", #"K", #"i", #"n", #"d"],
          [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #"K", #"i", #"n",
            #"d"]),
        ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"i",
           #"r", #"e", #"c", #"t", #"i", #"o", #"n"],
          [#"D", #"i", #"r", #"e", #"c", #"t", #"i", #"o", #"n"]),
        ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
           #"p", #"e", #"n", #"d", #"s"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"])],
      SGr_ls_ext
        ([([#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
             #"e", #"n", #"t"],
            Nprxy),
           ([#"P", #"r", #"T", #"y", #"p", #"e"], Nprxy),
           ([#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"], Nprxy),
           ([#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"], Nnrml),
           ([#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"], Nnrml),
           ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"], Nnrml),
           ([#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"], Nnrml),
           ([#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e", #"K", #"i", #"n",
              #"d"],
             Nenum),
           ([#"D", #"i", #"r", #"e", #"c", #"t", #"i", #"o", #"n"], Nenum)],
          [([#"E", #"I", #"S", #"u", #"p", #"P", #"r", #"o", #"p", #"e", #"r",
              #"t", #"y"],
             Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"r", #"i", #"a", #"b",
               #"l", #"e"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"F", #"l", #"o", #"w", #"P", #"o",
               #"r", #"t"],
              Einh),
            ([#"E", #"P", #"r", #"o", #"p", #"I", #"n", #"i", #"t"], Ereluni),
            ([#"E", #"P", #"r", #"o", #"p", #"T", #"y", #"p", #"e"], Ereluni),
            ([#"E", #"V", #"a", #"r", #"K", #"i", #"n", #"d"], Ereluni),
            ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"i",
               #"r", #"e", #"c", #"t", #"i", #"o", #"n"],
              Ereluni),
            ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
               #"p", #"e", #"n", #"d", #"s"],
              Ereluni),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
               #"e", #"m", #"e", #"n", #"t"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e"], Eref),
            ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"],
              Eref)],
          [], [([#"E", #"P", #"r", #"o", #"p", #"T", #"y", #"p", #"e"],
                 Sm (Val one_nat)),
                ([#"E", #"P", #"r", #"o", #"p", #"I", #"n", #"i", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"V", #"a", #"r", #"K", #"i", #"n", #"d"],
                  Sm (Val one_nat)),
                ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D",
                   #"i", #"r", #"e", #"c", #"t", #"i", #"o", #"n"],
                  Sm (Val one_nat)),
                ([#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D",
                   #"e", #"p", #"e", #"n", #"d", #"s"],
                  Sm Many)],
          ()));

val f_Props : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_Props,
      [([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t"],
         [#"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e", #"n",
           #"t"]),
        ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e"],
          [#"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g", #"2"],
          [#"S", #"t", #"r", #"i", #"n", #"g"])],
      ());

fun frdL (Mdl_ls_ext (gfgL, frdL, more)) = frdL;

fun consUMdlFs ml = consUFs (map snd (frdL ml));

val gFG_INTO_SysML_MM : unit gFGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
       [#"F", #"_", #"P", #"r", #"o", #"p", #"s"],
       [#"F", #"_", #"A", #"S", #"D"],
       [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
       [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
       [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
       [#"F", #"_", #"C", #"o", #"m", #"p", #"s"], [#"F", #"_", #"C", #"D"]],
      [[#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
        [#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
        [#"E", #"_", #"F", #"_", #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
        [#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
        [#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"D"],
        [#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"I", #"_", #"F", #"_",
          #"C", #"o", #"m", #"m", #"o", #"n"],
        [#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I", #"_",
          #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
        [#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I", #"_",
          #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
        [#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s", #"_", #"I",
          #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
        [#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_", #"I",
          #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
        [#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_", #"I",
          #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
        [#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_", #"I",
          #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I", #"_",
          #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I", #"_",
          #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
        [#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_", #"C",
          #"_", #"F", #"_", #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"C", #"_",
          #"F", #"_", #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_", #"C",
          #"_", #"F", #"_", #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_", #"B",
          #"l", #"o", #"c", #"k", #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_", #"V",
          #"T", #"y", #"p", #"e", #"s"]],
      [([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
         [#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D"], [#"F", #"_", #"C", #"D"]),
        ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s"],
          [#"F", #"_", #"C", #"o", #"m", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"I", #"_", #"F",
           #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"C", #"o", #"m", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"C", #"o", #"m", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
           #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"C",
           #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"C", #"o", #"m", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
           #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"C", #"D"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
           #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"C", #"D"])],
      [([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
         [#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s"],
          [#"F", #"_", #"C", #"o", #"m", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D"], [#"F", #"_", #"C", #"D"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"I", #"_", #"F",
           #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"]),
        ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
          [#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
           #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
          [#"F", #"_", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
           #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"]),
        ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
           #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"C",
           #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
           #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
          [#"F", #"_", #"A", #"S", #"D"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
           #"B", #"l", #"o", #"c", #"k", #"s"],
          [#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
           #"V", #"T", #"y", #"p", #"e", #"s"],
          [#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"])],
      GFGr_ls_ext
        ([([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"], Eimp),
           ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"], Eimp),
           ([#"E", #"_", #"F", #"_", #"A", #"S", #"D"], Eimp),
           ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"], Eimp),
           ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"], Eimp),
           ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"], Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s"], Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"D"], Eimp),
           ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"I", #"_", #"F",
              #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
              #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s", #"_", #"I",
              #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s", #"_",
              #"I", #"_", #"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
              #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
              #"I", #"_", #"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
              #"I", #"_", #"F", #"_", #"P", #"r", #"o", #"p", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
              #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"I",
              #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s", #"_",
              #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
             Econti),
           ([#"E", #"_", #"F", #"_", #"C", #"o", #"m", #"p", #"s", #"_", #"C",
              #"_", #"F", #"_", #"A", #"S", #"D"],
             Econti),
           ([#"E", #"_", #"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s", #"_",
              #"C", #"_", #"F", #"_", #"A", #"S", #"D"],
             Econti),
           ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
              #"B", #"l", #"o", #"c", #"k", #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"I", #"_", #"F", #"_",
              #"V", #"T", #"y", #"p", #"e", #"s"],
             Eimp)],
          ()));

val sG_F_VTypes : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e",
        #"n", #"t", #"3"],
       [#"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"],
       [#"P", #"r", #"P", #"T", #"y", #"p", #"e"],
       [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"],
       [#"L", #"i", #"t", #"e", #"r", #"a", #"l"],
       [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"],
       [#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"],
       [#"D", #"T", #"y", #"p", #"e"],
       [#"S", #"t", #"r", #"t", #"T", #"y", #"p", #"e"],
       [#"U", #"n", #"i", #"t", #"T", #"y", #"p", #"e"]],
      [[#"E", #"I", #"S", #"u", #"p", #"L", #"i", #"t", #"e", #"r", #"a", #"l"],
        [#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"l", #"u", #"e", #"T", #"y",
          #"p", #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"E", #"n", #"u", #"m", #"e", #"r", #"a",
          #"t", #"i", #"o", #"n"],
        [#"E", #"I", #"S", #"u", #"p", #"D", #"T", #"y", #"p", #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"t", #"T", #"y", #"p",
          #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"U", #"n", #"i", #"t", #"T", #"y", #"p",
          #"e"],
        [#"E", #"P", #"r", #"o", #"p", #"s"],
        [#"E", #"L", #"i", #"t", #"e", #"r", #"a", #"l", #"s"],
        [#"E", #"S", #"u", #"p", #"e", #"r"], [#"E", #"U", #"n", #"i", #"t"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"3"],
        [#"E", #"R", #"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
          #"y"],
        [#"E", #"R", #"P", #"r", #"P", #"T", #"y", #"p", #"e"],
        [#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"]],
      [([#"E", #"I", #"S", #"u", #"p", #"L", #"i", #"t", #"e", #"r", #"a",
          #"l"],
         [#"L", #"i", #"t", #"e", #"r", #"a", #"l"]),
        ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"l", #"u", #"e", #"T",
           #"y", #"p", #"e"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"E", #"n", #"u", #"m", #"e", #"r",
           #"a", #"t", #"i", #"o", #"n"],
          [#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"]),
        ([#"E", #"I", #"S", #"u", #"p", #"D", #"T", #"y", #"p", #"e"],
          [#"D", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"t", #"T", #"y",
           #"p", #"e"],
          [#"S", #"t", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"U", #"n", #"i", #"t", #"T", #"y",
           #"p", #"e"],
          [#"U", #"n", #"i", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"P", #"r", #"o", #"p", #"s"],
          [#"S", #"t", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"L", #"i", #"t", #"e", #"r", #"a", #"l", #"s"],
          [#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"]),
        ([#"E", #"S", #"u", #"p", #"e", #"r"], [#"D", #"T", #"y", #"p", #"e"]),
        ([#"E", #"U", #"n", #"i", #"t"],
          [#"U", #"n", #"i", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"3"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"3"]),
        ([#"E", #"R", #"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
           #"y"],
          [#"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"R", #"P", #"r", #"P", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"])],
      [([#"E", #"I", #"S", #"u", #"p", #"L", #"i", #"t", #"e", #"r", #"a",
          #"l"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t", #"3"]),
        ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"l", #"u", #"e", #"T",
           #"y", #"p", #"e"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"3"]),
        ([#"E", #"I", #"S", #"u", #"p", #"E", #"n", #"u", #"m", #"e", #"r",
           #"a", #"t", #"i", #"o", #"n"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"D", #"T", #"y", #"p", #"e"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"t", #"T", #"y",
           #"p", #"e"],
          [#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"U", #"n", #"i", #"t", #"T", #"y",
           #"p", #"e"],
          [#"D", #"T", #"y", #"p", #"e"]),
        ([#"E", #"P", #"r", #"o", #"p", #"s"],
          [#"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"L", #"i", #"t", #"e", #"r", #"a", #"l", #"s"],
          [#"L", #"i", #"t", #"e", #"r", #"a", #"l"]),
        ([#"E", #"S", #"u", #"p", #"e", #"r"],
          [#"P", #"r", #"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"U", #"n", #"i", #"t"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"3"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"3"]),
        ([#"E", #"R", #"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
           #"y"],
          [#"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"R", #"P", #"r", #"P", #"T", #"y", #"p", #"e"],
          [#"P", #"r", #"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"],
          [#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"])],
      SGr_ls_ext
        ([([#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
             #"e", #"n", #"t", #"3"],
            Nprxy),
           ([#"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"],
             Nprxy),
           ([#"P", #"r", #"P", #"T", #"y", #"p", #"e"], Nprxy),
           ([#"L", #"i", #"t", #"e", #"r", #"a", #"l"], Nnrml),
           ([#"V", #"a", #"l", #"u", #"e", #"T", #"y", #"p", #"e"], Nabst),
           ([#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"],
             Nnrml),
           ([#"D", #"T", #"y", #"p", #"e"], Nnrml),
           ([#"S", #"t", #"r", #"t", #"T", #"y", #"p", #"e"], Nnrml),
           ([#"U", #"n", #"i", #"t", #"T", #"y", #"p", #"e"], Nnrml),
           ([#"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"], Nprxy)],
          [([#"E", #"I", #"S", #"u", #"p", #"L", #"i", #"t", #"e", #"r", #"a",
              #"l"],
             Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"V", #"a", #"l", #"u", #"e", #"T",
               #"y", #"p", #"e"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"E", #"n", #"u", #"m", #"e", #"r",
               #"a", #"t", #"i", #"o", #"n"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"D", #"T", #"y", #"p", #"e"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"t", #"T", #"y",
               #"p", #"e"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"U", #"n", #"i", #"t", #"T", #"y",
               #"p", #"e"],
              Einh),
            ([#"E", #"P", #"r", #"o", #"p", #"s"], Ecompuni),
            ([#"E", #"L", #"i", #"t", #"e", #"r", #"a", #"l", #"s"], Ecompuni),
            ([#"E", #"S", #"u", #"p", #"e", #"r"], Ereluni),
            ([#"E", #"U", #"n", #"i", #"t"], Ereluni),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
               #"e", #"m", #"e", #"n", #"t", #"3"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
               #"y"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"P", #"T", #"y", #"p", #"e"], Eref),
            ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"],
              Eref)],
          [], [([#"E", #"P", #"r", #"o", #"p", #"s"], Sm Many),
                ([#"E", #"L", #"i", #"t", #"e", #"r", #"a", #"l", #"s"],
                  Sm Many),
                ([#"E", #"S", #"u", #"p", #"e", #"r"], Sm Many),
                ([#"E", #"U", #"n", #"i", #"t"], Sm (Val one_nat))],
          ()));

val f_VTypes : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_VTypes,
      [([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"3"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"P", #"r", #"o", #"p", #"e", #"r", #"t",
           #"y"],
          [#"P", #"r", #"o", #"p", #"e", #"r", #"t", #"y"]),
        ([#"E", #"R", #"P", #"r", #"P", #"T", #"y", #"p", #"e"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"S", #"t", #"r", #"i", #"n", #"g"],
          [#"S", #"t", #"r", #"i", #"n", #"g"])],
      ());

val tF_VTypes : unit tFr_ls_ext = TFr_ls_ext (f_VTypes, [], ());

val sG_F_PTypes : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"T", #"y", #"p", #"e", #"2"],
       [#"P", #"T", #"y", #"p", #"e"], [#"R", #"e", #"a", #"l"],
       [#"I", #"n", #"t"], [#"N", #"a", #"t"], [#"B", #"o", #"o", #"l"],
       [#"S", #"t", #"r", #"i", #"n", #"g"],
       [#"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l"]],
      [[#"E", #"I", #"S", #"u", #"p", #"P", #"T", #"y", #"p", #"e"],
        [#"E", #"I", #"S", #"u", #"p", #"R", #"e", #"a", #"l"],
        [#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t"],
        [#"E", #"I", #"S", #"u", #"p", #"N", #"a", #"t"],
        [#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"i", #"n", #"g"],
        [#"E", #"I", #"S", #"u", #"p", #"B", #"o", #"o", #"l"],
        [#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t", #"e", #"r", #"v", #"a",
          #"l"],
        [#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"l",
          #"b"],
        [#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"u",
          #"b"],
        [#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e", #"2"]],
      [([#"E", #"I", #"S", #"u", #"p", #"P", #"T", #"y", #"p", #"e"],
         [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"R", #"e", #"a", #"l"],
          [#"R", #"e", #"a", #"l"]),
        ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t"], [#"I", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"N", #"a", #"t"], [#"N", #"a", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"B", #"o", #"o", #"l"],
          [#"B", #"o", #"o", #"l"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"i", #"n", #"g"],
          [#"S", #"t", #"r", #"i", #"n", #"g"]),
        ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t", #"e", #"r", #"v",
           #"a", #"l"],
          [#"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l"]),
        ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"l",
           #"b"],
          [#"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l"]),
        ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"u",
           #"b"],
          [#"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l"]),
        ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e", #"2"],
          [#"P", #"r", #"T", #"y", #"p", #"e", #"2"])],
      [([#"E", #"I", #"S", #"u", #"p", #"P", #"T", #"y", #"p", #"e"],
         [#"P", #"r", #"T", #"y", #"p", #"e", #"2"]),
        ([#"E", #"I", #"S", #"u", #"p", #"R", #"e", #"a", #"l"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"N", #"a", #"t"], [#"I", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"B", #"o", #"o", #"l"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"i", #"n", #"g"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t", #"e", #"r", #"v",
           #"a", #"l"],
          [#"P", #"T", #"y", #"p", #"e"]),
        ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"l",
           #"b"],
          [#"I", #"n", #"t"]),
        ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"u",
           #"b"],
          [#"I", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e", #"2"],
          [#"P", #"r", #"T", #"y", #"p", #"e", #"2"])],
      SGr_ls_ext
        ([([#"P", #"r", #"T", #"y", #"p", #"e", #"2"], Nprxy),
           ([#"P", #"T", #"y", #"p", #"e"], Nnrml),
           ([#"R", #"e", #"a", #"l"], Nnrml), ([#"I", #"n", #"t"], Nnrml),
           ([#"N", #"a", #"t"], Nnrml), ([#"B", #"o", #"o", #"l"], Nnrml),
           ([#"S", #"t", #"r", #"i", #"n", #"g"], Nenum),
           ([#"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l"], Nenum)],
          [([#"E", #"I", #"S", #"u", #"p", #"P", #"T", #"y", #"p", #"e"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"R", #"e", #"a", #"l"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"N", #"a", #"t"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"B", #"o", #"o", #"l"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"S", #"t", #"r", #"i", #"n", #"g"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"I", #"n", #"t", #"e", #"r", #"v",
               #"a", #"l"],
              Einh),
            ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"l",
               #"b"],
              Ereluni),
            ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_", #"u",
               #"b"],
              Ereluni),
            ([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e", #"2"], Eref)],
          [], [([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_",
                  #"l", #"b"],
                 Sm (Val one_nat)),
                ([#"E", #"I", #"n", #"t", #"e", #"r", #"v", #"a", #"l", #"_",
                   #"u", #"b"],
                  Sm (Val one_nat))],
          ()));

val f_PTypes : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_PTypes,
      [([#"E", #"R", #"P", #"r", #"T", #"y", #"p", #"e", #"2"],
         [#"T", #"y", #"p", #"e"])],
      ());

val tF_PTypes : unit tFr_ls_ext = TFr_ls_ext (f_PTypes, [], ());

val sG_F_Common : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e", #"n", #"t"],
       [#"T", #"y", #"p", #"e"]],
      [], [], [],
      SGr_ls_ext
        ([([#"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e", #"n",
             #"t"],
            Nnrml),
           ([#"T", #"y", #"p", #"e"], Nnrml)],
          [], [], [], ()));

val f_Common : unit fr_ls_ext = Fr_ls_ext (sG_F_Common, [], ());

val tF_Common : unit tFr_ls_ext = TFr_ls_ext (f_Common, [], ());

val sG_F_Blocks : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m", #"e",
        #"n", #"t", #"2"],
       [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"],
       [#"B", #"l", #"o", #"c", #"k"],
       [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K", #"i", #"n",
         #"d"],
       [#"S", #"y", #"s", #"t", #"e", #"m"],
       [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"],
       [#"M", #"o", #"d", #"e", #"l", #"K", #"i", #"n", #"d"],
       [#"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
       [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"],
       [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"],
       [#"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"]],
      [[#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k"],
        [#"E", #"I", #"S", #"u", #"p", #"S", #"y", #"s", #"t", #"e", #"m"],
        [#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"m", #"p", #"o", #"n", #"e",
          #"n", #"t"],
        [#"E", #"I", #"S", #"u", #"p", #"E", #"C", #"o", #"m", #"p", #"o", #"n",
          #"e", #"n", #"t"],
        [#"E", #"I", #"S", #"u", #"p", #"P", #"O", #"C", #"o", #"m", #"p", #"o",
          #"n", #"e", #"n", #"t"],
        [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"],
        [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"V", #"a",
          #"r", #"s"],
        [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K", #"i",
          #"n", #"d"],
        [#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"M",
          #"o", #"d", #"e", #"l", #"T", #"y"],
        [#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"P",
          #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
        [#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"2"],
        [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
          #"t"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
          #"e"]],
      [([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k"],
         [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"y", #"s", #"t", #"e", #"m"],
          [#"S", #"y", #"s", #"t", #"e", #"m"]),
        ([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"m", #"p", #"o", #"n",
           #"e", #"n", #"t"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"E", #"C", #"o", #"m", #"p", #"o",
           #"n", #"e", #"n", #"t"],
          [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"P", #"O", #"C", #"o", #"m", #"p",
           #"o", #"n", #"e", #"n", #"t"],
          [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"],
          [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"V",
           #"a", #"r", #"s"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K",
           #"i", #"n", #"d"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
           #"M", #"o", #"d", #"e", #"l", #"T", #"y"],
          [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
           #"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
          [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"2"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
           #"e"],
          [#"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"])],
      [([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t", #"2"]),
        ([#"E", #"I", #"S", #"u", #"p", #"S", #"y", #"s", #"t", #"e", #"m"],
          [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"m", #"p", #"o", #"n",
           #"e", #"n", #"t"],
          [#"B", #"l", #"o", #"c", #"k"]),
        ([#"E", #"I", #"S", #"u", #"p", #"E", #"C", #"o", #"m", #"p", #"o",
           #"n", #"e", #"n", #"t"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"I", #"S", #"u", #"p", #"P", #"O", #"C", #"o", #"m", #"p",
           #"o", #"n", #"e", #"n", #"t"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
        ([#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"V",
           #"a", #"r", #"s"],
          [#"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K",
           #"i", #"n", #"d"],
          [#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K", #"i",
            #"n", #"d"]),
        ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
           #"M", #"o", #"d", #"e", #"l", #"T", #"y"],
          [#"M", #"o", #"d", #"e", #"l", #"K", #"i", #"n", #"d"]),
        ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
           #"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
          [#"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"]),
        ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
           #"e", #"m", #"e", #"n", #"t", #"2"],
          [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
            #"e", #"n", #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t"],
          [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
           #"e"],
          [#"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"])],
      SGr_ls_ext
        ([([#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
             #"e", #"n", #"t", #"2"],
            Nprxy),
           ([#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"],
             Nprxy),
           ([#"B", #"l", #"o", #"c", #"k"], Nnrml),
           ([#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K", #"i",
              #"n", #"d"],
             Nenum),
           ([#"S", #"y", #"s", #"t", #"e", #"m"], Nnrml),
           ([#"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"], Nnrml),
           ([#"M", #"o", #"d", #"e", #"l", #"K", #"i", #"n", #"d"], Nenum),
           ([#"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"], Nenum),
           ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"],
             Nnrml),
           ([#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"],
             Nnrml),
           ([#"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"],
             Nprxy)],
          [([#"E", #"I", #"S", #"u", #"p", #"B", #"l", #"o", #"c", #"k"], Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"S", #"y", #"s", #"t", #"e", #"m"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"C", #"o", #"m", #"p", #"o", #"n",
               #"e", #"n", #"t"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"E", #"C", #"o", #"m", #"p", #"o",
               #"n", #"e", #"n", #"t"],
              Einh),
            ([#"E", #"I", #"S", #"u", #"p", #"P", #"O", #"C", #"o", #"m", #"p",
               #"o", #"n", #"e", #"n", #"t"],
              Einh),
            ([#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"V",
               #"a", #"r", #"s"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t", #"K",
               #"i", #"n", #"d"],
              Ereluni),
            ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
               #"M", #"o", #"d", #"e", #"l", #"T", #"y"],
              Ereluni),
            ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
               #"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
              Ereluni),
            ([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l",
               #"e", #"m", #"e", #"n", #"t", #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
               #"t"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
               #"e"],
              Eref)],
          [], [([#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p",
                  #"s"],
                 Sm Many),
                ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
                   #"V", #"a", #"r", #"s"],
                  Sm Many),
                ([#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t",
                   #"K", #"i", #"n", #"d"],
                  Sm (Val one_nat)),
                ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n",
                   #"t", #"M", #"o", #"d", #"e", #"l", #"T", #"y"],
                  Sm (Val one_nat)),
                ([#"E", #"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n",
                   #"t", #"P", #"l", #"a", #"t", #"f", #"o", #"r", #"m"],
                  Sm (Val one_nat))],
          ()));

val f_Blocks : unit fr_ls_ext =
  Fr_ls_ext
    (sG_F_Blocks,
      [([#"E", #"R", #"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e",
          #"m", #"e", #"n", #"t", #"2"],
         [#"P", #"r", #"N", #"a", #"m", #"e", #"d", #"E", #"l", #"e", #"m",
           #"e", #"n", #"t"]),
        ([#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
           #"t"],
          [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"r", #"i", #"a", #"b", #"l",
           #"e"],
          [#"V", #"a", #"r", #"i", #"a", #"b", #"l", #"e"])],
      ());

val tF_Blocks : unit tFr_ls_ext = TFr_ls_ext (f_Blocks, [], ());

val tF_Props : unit tFr_ls_ext = TFr_ls_ext (f_Props, [], ());

val tF_Comps : unit tFr_ls_ext = TFr_ls_ext (f_Comps, [], ());

val iNTO_SysML_MM_T : unit tyMdl_ls_ext =
  TyMdl_ls_ext
    (gFG_INTO_SysML_MM,
      [([#"F", #"_", #"C", #"o", #"m", #"m", #"o", #"n"], tF_Common),
        ([#"F", #"_", #"P", #"r", #"o", #"p", #"s"], tF_Props),
        ([#"F", #"_", #"A", #"S", #"D"], tF_ASD),
        ([#"F", #"_", #"B", #"l", #"o", #"c", #"k", #"s"], tF_Blocks),
        ([#"F", #"_", #"P", #"T", #"y", #"p", #"e", #"s"], tF_PTypes),
        ([#"F", #"_", #"V", #"T", #"y", #"p", #"e", #"s"], tF_VTypes),
        ([#"F", #"_", #"C", #"o", #"m", #"p", #"s"], tF_Comps),
        ([#"F", #"_", #"C", #"D"], tF_CD)],
      ());

val t_F_ASD_3WTs : unit morphL_ext =
  MorphL_ext
    ([([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A", #"S",
         #"D"],
        [#"A", #"S", #"D"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S", #"y",
          #"s"],
         [#"S", #"y", #"s", #"t", #"e", #"m"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"1"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"2"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"3"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
          #"1"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
          #"2"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r", #"T",
          #"a", #"n", #"k"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r", #"T",
          #"a", #"n", #"k"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e"],
         [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
         [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
         [#"D", #"T", #"y", #"p", #"e"]),
       ([#"A", #"r", #"e", #"a"], [#"D", #"T", #"y", #"p", #"e"]),
       ([#"H", #"e", #"i", #"g", #"h", #"t"], [#"D", #"T", #"y", #"p", #"e"]),
       ([#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
         [#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"i",
          #"n"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"o",
          #"u", #"t"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e", #"_", #"w"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"v",
          #"1"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"])],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"o", #"u", #"t"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
            #"p", #"e", #"n", #"d", #"s"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
            #"p", #"e", #"n", #"d", #"s"])],
      ());

val t_F_CD_3WTs : unit morphL_ext =
  MorphL_ext
    ([([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
        [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
          #"o", #"l", #"1"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
          #"o", #"l", #"2"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
          #"r"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"C", #"D", #"_", #"3", #"W", #"T", #"s"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
           #"D", #"i", #"a", #"g", #"r", #"a", #"m"]),
       ([#"W", #"T", #"S", #"y", #"s"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"V"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"1"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"2"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"3"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"C"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"T", #"C", #"1"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"T", #"C", #"2"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
          #"2"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
          #"3"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"v", #"1", #"_", #"v", #"2"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"v", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"v", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"3"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"3"], [#"P", #"o", #"r", #"t"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"i", #"n"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"o", #"u", #"t"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"v", #"1"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"])],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"V", #"_", #"w"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"])],
      ());

val mdlTy_3WTs : unit mdlTy_ls_ext =
  MdlTy_ls_ext
    (iNTO_SysML_MM_T, mdl_3WTs, consUGM t_F_ASD_3WTs t_F_CD_3WTs, ());

fun edgesOfMMTy fl m e =
  filtera (fn ea => equal_optiona (equal_list equal_char) (fE m ea) (SOME e))
    ((esG o sg_ls) fl);

fun nodesOfMMTy fl m vty =
  filtera (fn v => equal_optiona (equal_list equal_char) (fV m v) (SOME vty))
    ((nsG o sg_ls) fl);

fun getSrcPortOfC m fl v =
  tgt (sg (toFr fl))
    (the (find (fn e =>
                 equal_optiona (equal_list equal_char) (src (sg (toFr fl)) e)
                   (SOME v))
           (edgesOfMMTy fl m [#"E", #"C", #"_", #"s", #"r", #"c"])));

fun getTgtPortOfC m fl v =
  tgt (sg (toFr fl))
    (the (find (fn e =>
                 equal_optiona (equal_list equal_char) (src (sg (toFr fl)) e)
                   (SOME v))
           (edgesOfMMTy fl m [#"E", #"C", #"_", #"t", #"g", #"t"])));

fun removeDupNsGL gl =
  Gr_ls_ext
    (remdups (equal_list equal_char) (nsG gl), esG gl, srcG gl, tgtG gl, ());

fun mdlL (MdlTy_ls_ext (tmdlL, mdlL, mtyL, more)) = mdlL;

fun mtyL (MdlTy_ls_ext (tmdlL, mdlL, mtyL, more)) = mtyL;

fun getFlowPortTypeOfPort m fl v =
  the (tgt (sg (toFr fl))
        (hd (filtera
              (fn e =>
                equal_optiona (equal_list equal_char) (src (sg (toFr fl)) e)
                  (SOME v) andalso
                  (equal_optiona (equal_list equal_char) (fE m e)
                     (SOME [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p",
                             #"e"]) andalso
                    equal_optiona (equal_list equal_char)
                      (fV m (the (tgt (sg (toFr fl)) e)))
                      (SOME [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o",
                              #"r", #"t", #"2"])))
              ((esG o sg_ls) fl))));

fun getBlockInstanceOfPort m fl v =
  the (src (sg (toFr fl))
        (hd (filtera
              (fn e =>
                equal_optiona (equal_list equal_char) (tgt (sg (toFr fl)) e)
                  (SOME v) andalso
                  equal_optiona (equal_list equal_char) (fE m e)
                    (SOME [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]))
              ((esG o sg_ls) fl))));

fun getOtherInternalPorts m fl v =
  let
    val v_bi = getBlockInstanceOfPort m fl v;
  in
    map the
      (map_filter
        (fn x =>
          (if equal_optiona (equal_list equal_char) (fE m x)
                (SOME [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]) andalso
                (equal_optiona (equal_list equal_char) (src (sg (toFr fl)) x)
                   (SOME v_bi) andalso
                  not (equal_optiona (equal_list equal_char)
                        (tgt (sg (toFr fl)) x) (SOME v)))
            then SOME (tgt (sg (toFr fl)) x) else NONE))
        ((esG o sg_ls) fl))
  end;

fun getDependentPortOfV m fl v depFPs =
  the (tgt (sg (toFr fl))
        (the (find (fn e =>
                     equal_optiona (equal_list equal_char) (fE m e)
                       (SOME [#"E", #"B", #"I", #"p", #"o", #"r", #"t",
                               #"s"]) andalso
                       (equal_optiona (equal_list equal_char)
                          (src (sg (toFr fl)) e)
                          (SOME (getBlockInstanceOfPort m fl v)) andalso
                         (membera (equal_list equal_char)
                            (getOtherInternalPorts m fl v)
                            (the (tgt (sg (toFr fl)) e)) andalso
                           member (equal_list equal_char)
                             (getFlowPortTypeOfPort m fl
                               (the (tgt (sg (toFr fl)) e)))
                             depFPs)))
               ((esG o sg_ls) fl))));

fun consGlFrNodePair f v1 v2 =
  let
    val e = [#"E", #"_"] @ v1 @ [#"_"] @ v2;
  in
    Gr_ls_ext ([v1, v2], [e], [(e, v1)], [(e, v2)], ())
  end;

fun consGLFrDepends m fl v [] evps = emptyGL
  | consGLFrDepends m fl v (e :: es) evps =
    let
      val vdeps =
        Set (map_filter
              (fn x =>
                (if equal_lista equal_char (fst x) e then SOME (snd x)
                  else NONE))
              evps);
    in
      consUG (consGlFrNodePair (toFr fl) (getDependentPortOfV m fl v vdeps) v)
        (consGLFrDepends m fl v es evps)
    end;

fun buildGrForPort m fl [] evpsSrc evpsTgt = emptyGL
  | buildGrForPort m fl (v :: vs) evpsSrc evpsTgt =
    consUG
      (consGLFrDepends m fl v
        (map_filter
          (fn x =>
            (if equal_lista equal_char (snd x) (getFlowPortTypeOfPort m fl v)
              then SOME (fst x) else NONE))
          evpsSrc)
        evpsTgt)
      (buildGrForPort m fl vs evpsSrc evpsTgt);

fun buildGrForInternalDependenciesOfPorts m fl =
  buildGrForPort m fl (nodesOfMMTy fl m [#"P", #"o", #"r", #"t"])
    (filtera
      (fn p =>
        membera (equal_list equal_char)
          (edgesOfMMTy fl m
            [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
              #"p", #"e", #"n", #"d", #"s"])
          (fst p))
      (consSrcStF fl))
    (filtera
      (fn p =>
        membera (equal_list equal_char)
          (edgesOfMMTy fl m
            [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
              #"p", #"e", #"n", #"d", #"s"])
          (fst p))
      (consTgtStF fl));

fun buildGrForConnectors m fl [] = emptyGL
  | buildGrForConnectors m fl (v :: vs) =
    consUG
      (consGlFrNodePair (toFr fl) (the (getSrcPortOfC m fl v))
        (the (getTgtPortOfC m fl v)))
      (buildGrForConnectors m fl vs);

fun iNTO_SysML_toPDG_GL m fl =
  removeDupNsGL
    (consUG
      (buildGrForConnectors m fl
        (nodesOfMMTy fl m
          [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]))
      (buildGrForInternalDependenciesOfPorts m fl));

fun iNTO_SysML_toPDG mlt =
  iNTO_SysML_toPDG_GL (toMorph (mtyL mlt)) (consUMdlFs (mdlL mlt));

val gFG_3WTs_loop : unit gFGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
        #"o", #"o", #"p"],
       [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l", #"o",
         #"o", #"p"]],
      [[#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
         #"A", #"S", #"D"],
        [#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
          #"s"],
        [#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"]],
      [([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
          #"A", #"S", #"D"],
         [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
           #"o", #"o", #"p"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
           #"s"],
          [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
            #"l", #"o", #"o", #"p"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
          [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
            #"o", #"o", #"p"])],
      [([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
          #"A", #"S", #"D"],
         [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
           #"l", #"o", #"o", #"p"]),
        ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
           #"s"],
          [#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s", #"_",
            #"l", #"o", #"o", #"p"]),
        ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
          [#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
            #"o", #"o", #"p"])],
      GFGr_ls_ext
        ([([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s",
             #"_", #"A", #"S", #"D"],
            Eimp),
           ([#"E", #"_", #"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T",
              #"s"],
             Eimp),
           ([#"E", #"_", #"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s"],
             Eimp)],
          ()));

val sG_ASD_3WTs_loop : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A", #"S",
        #"D"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S", #"y",
         #"s"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"1"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"2"],
       [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
         #"k", #"s", #"S", #"y", #"s", #"3"],
       [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
         #"1"],
       [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
         #"2"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
         #"n", #"k"],
       [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
         #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
         #"n", #"k"],
       [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
       [#"V", #"a", #"l", #"v", #"e"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
       [#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
       [#"A", #"r", #"e", #"a"], [#"H", #"e", #"i", #"g", #"h", #"t"],
       [#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"i",
         #"n"],
       [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"o",
         #"u", #"t"],
       [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
       [#"V", #"a", #"l", #"v", #"e", #"_", #"w"],
       [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"v",
         #"1"],
       [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"w",
         #"i", #"n"]],
      [[#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
         #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
         #"s", #"S", #"y", #"s"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
        [#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s",
          #"e", #"d"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
          #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e",
          #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e",
          #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
        [#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
          #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
          #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
        [#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"i", #"n"],
        [#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"o", #"u", #"t"],
        [#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
        [#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
        [#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"v", #"1"],
        [#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"w", #"i", #"n"],
        [#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
        [#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_", #"w",
          #"i", #"n"],
        [#"E", #"_", #"D", #"e", #"p", #"_", #"v", #"1", #"_", #"w", #"i",
          #"n"]],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
           #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
            #"S", #"D"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"3"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
            #"n", #"k", #"s", #"S", #"y", #"s", #"3"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
            #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
            #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"w", #"i", #"n"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"v", #"1", #"_", #"w", #"i",
           #"n"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"v", #"1"])],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
           #"y", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"A", #"r", #"e", #"a"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"H", #"e", #"i", #"g", #"h", #"t"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
            #"y", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"v", #"1"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"w", #"i", #"n"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"w", #"i", #"n"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"v", #"1", #"_", #"w", #"i",
           #"n"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"w", #"i", #"n"])],
      SGr_ls_ext
        ([([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
             #"S", #"D"],
            Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S",
              #"y", #"s"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"1"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"2"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s", #"3"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r",
              #"T", #"a", #"n", #"k"],
             Nnrml),
           ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
              #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r",
              #"T", #"a", #"n", #"k"],
             Nnrml),
           ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
              #"l", #"1"],
             Nnrml),
           ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
              #"l", #"2"],
             Nnrml),
           ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
             Nnrml),
           ([#"V", #"a", #"l", #"v", #"e"], Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"], Nnrml),
           ([#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"], Nnrml),
           ([#"A", #"r", #"e", #"a"], Nnrml),
           ([#"H", #"e", #"i", #"g", #"h", #"t"], Nnrml),
           ([#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
             Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
              #"i", #"n"],
             Nnrml),
           ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
              #"o", #"u", #"t"],
             Nnrml),
           ([#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"], Nnrml),
           ([#"V", #"a", #"l", #"v", #"e", #"_", #"w"], Nnrml),
           ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
              #"v", #"1"],
             Nnrml),
           ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
              #"w", #"i", #"n"],
             Nnrml)],
          [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
              #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
              #"n", #"k", #"s", #"S", #"y", #"s"],
             Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"1"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"2"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
               #"e"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
              Elnk),
            ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
               #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
               #"s", #"e", #"d"],
              Elnk),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
               #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
               #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
               #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
               #"e", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
               #"e", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
               #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
               #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
              Ecompuni),
            ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
               #"_", #"w", #"i", #"n"],
              Elnk),
            ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
               #"_", #"w", #"o", #"u", #"t"],
              Elnk),
            ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"], Elnk),
            ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
               #"r", #"_", #"v", #"1"],
              Elnk),
            ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
               #"r", #"_", #"w", #"i", #"n"],
              Elnk),
            ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
               #"w", #"i", #"n"],
              Elnk),
            ([#"E", #"_", #"D", #"e", #"p", #"_", #"v", #"1", #"_", #"w", #"i",
               #"n"],
              Elnk)],
          [], [([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                  #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_",
                  #"s", #"r", #"c"],
                 Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_",
                   #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_",
                   #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r",
                   #"T", #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_",
                   #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a",
                   #"l", #"v", #"e", #"_", #"s", #"r", #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r",
                   #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r",
                   #"c"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a",
                   #"l", #"v", #"e", #"_", #"t", #"g", #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g",
                   #"t"],
                  Sm (Val one_nat)),
                ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s",
                   #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a",
                   #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g",
                   #"t"],
                  Sm (Val (nat_of_num (Bit0 One))))],
          ()));

val f_ASD_3WTs_loop : unit fr_ls_ext = Fr_ls_ext (sG_ASD_3WTs_loop, [], ());

val sG_CD_3WTs_loop : unit sGr_ls_ext gr_ls_ext =
  Gr_ls_ext
    ([[#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e"],
       [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
         #"o", #"l", #"1"],
       [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
         #"o", #"l", #"2"],
       [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
       [#"C", #"D", #"_", #"3", #"W", #"T", #"s"],
       [#"W", #"T", #"S", #"y", #"s"], [#"V"], [#"W", #"T", #"1"],
       [#"W", #"T", #"2"], [#"W", #"T", #"3"], [#"C"], [#"T", #"C", #"1"],
       [#"T", #"C", #"2"], [#"v", #"1"], [#"v", #"2"], [#"w"],
       [#"w", #"i", #"n", #"1"], [#"w", #"o", #"u", #"t", #"1"],
       [#"w", #"i", #"n", #"2"], [#"w", #"o", #"u", #"t", #"2"],
       [#"w", #"i", #"n", #"3"], [#"w", #"o", #"u", #"t", #"3"],
       [#"w", #"i", #"n"], [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"],
       [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n", #"2"],
       [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n", #"3"],
       [#"C", #"_", #"v", #"1", #"_", #"v", #"2"],
       [#"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i", #"n"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
       [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
       [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
         #"w", #"i", #"n"],
       [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
         #"w", #"o", #"u", #"t"],
       [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
         #"_", #"v", #"1"],
       [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
         #"_", #"w", #"i", #"n"]],
      [[#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
        [#"E", #"C", #"D", #"_", #"V"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
        [#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
        [#"E", #"C", #"D", #"_", #"C"],
        [#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
        [#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
          #"1"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_",
          #"w", #"i", #"n", #"2"],
        [#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_",
          #"w", #"i", #"n", #"3"],
        [#"E", #"_", #"C", #"_", #"v", #"1"],
        [#"E", #"_", #"C", #"_", #"w", #"i", #"n"],
        [#"E", #"_", #"V", #"_", #"v", #"2"], [#"E", #"_", #"V", #"_", #"w"],
        [#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
        [#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
        [#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
        [#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
        [#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
        [#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
        [#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s", #"r",
          #"c"],
        [#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t", #"g",
          #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_", #"s",
          #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_", #"t",
          #"g", #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i",
          #"n", #"2", #"_", #"s", #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i",
          #"n", #"2", #"_", #"t", #"g", #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i",
          #"n", #"3", #"_", #"s", #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i",
          #"n", #"3", #"_", #"t", #"g", #"t"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i",
          #"n", #"_", #"s", #"r", #"c"],
        [#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i",
          #"n", #"_", #"t", #"g", #"t"],
        [#"E", #"T", #"C", #"1", #"_", #"V"],
        [#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"],
        [#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"],
        [#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
        [#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"],
        [#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"_", #"t", #"y"],
        [#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
        [#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
        [#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1"],
        [#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l",
          #"e", #"r"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
          #"2"],
        [#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"_", #"w", #"i", #"n"],
        [#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"_", #"w", #"o", #"u", #"t"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l",
          #"e", #"r", #"_", #"v", #"1"],
        [#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l",
          #"e", #"r", #"_", #"w", #"i", #"n"]],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"C", #"D", #"_", #"3", #"W", #"T", #"s"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"], [#"C"]),
        ([#"E", #"_", #"C", #"_", #"w", #"i", #"n"], [#"C"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"], [#"V"]),
        ([#"E", #"_", #"V", #"_", #"w"], [#"V"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"W", #"T", #"1"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"W", #"T", #"1"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"W", #"T", #"2"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"W", #"T", #"2"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"W", #"T", #"3"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"W", #"T", #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"s", #"r", #"c"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"t", #"g", #"t"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i", #"n"]),
        ([#"E", #"T", #"C", #"1", #"_", #"V"], [#"T", #"C", #"1"]),
        ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], [#"T", #"C", #"1"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], [#"T", #"C", #"2"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], [#"T", #"C", #"2"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"],
          [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"], [#"v", #"1"]),
        ([#"E", #"_", #"w", #"i", #"n", #"_", #"t", #"y"], [#"w", #"i", #"n"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"], [#"v", #"2"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"], [#"w"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"w", #"o", #"u", #"t", #"3"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"w", #"i", #"n"])],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"W", #"T", #"S", #"y", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"], [#"V"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"], [#"W", #"T", #"1"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"], [#"W", #"T", #"2"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"], [#"W", #"T", #"3"]),
        ([#"E", #"C", #"D", #"_", #"C"], [#"C"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"], [#"T", #"C", #"1"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"], [#"T", #"C", #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"C", #"_", #"v", #"1", #"_", #"v", #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
            #"2"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
            #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"], [#"v", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"i", #"n"], [#"w", #"i", #"n"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"], [#"v", #"2"]),
        ([#"E", #"_", #"V", #"_", #"w"], [#"w"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"w", #"o", #"u", #"t", #"3"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"v", #"1"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"v", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"w"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"w", #"o", #"u", #"t", #"1"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"w", #"o", #"u", #"t", #"2"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"w", #"i", #"n", #"3"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"s", #"r", #"c"],
          [#"w", #"o", #"u", #"t", #"3"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"t", #"g", #"t"],
          [#"w", #"i", #"n"]),
        ([#"E", #"T", #"C", #"1", #"_", #"V"], [#"V"]),
        ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], [#"W", #"T", #"1"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], [#"W", #"T", #"2"]),
        ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], [#"W", #"T", #"3"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
          [#"T", #"C", #"1"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
          [#"T", #"C", #"2"]),
        ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"], [#"C"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"]),
        ([#"E", #"_", #"w", #"i", #"n", #"_", #"t", #"y"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
            #"r", #"o", #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
            #"_", #"w", #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"v", #"1"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"w", #"i", #"n"],
          [#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
            #"r", #"_", #"w", #"i", #"n"])],
      SGr_ls_ext
        ([([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
            Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e"], Nprxy),
           ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
              #"r", #"o", #"l", #"1"],
             Nprxy),
           ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t",
              #"r", #"o", #"l", #"2"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
              #"r"],
             Nprxy),
           ([#"C", #"D", #"_", #"3", #"W", #"T", #"s"], Nnrml),
           ([#"W", #"T", #"S", #"y", #"s"], Nnrml), ([#"V"], Nnrml),
           ([#"W", #"T", #"1"], Nnrml), ([#"W", #"T", #"2"], Nnrml),
           ([#"W", #"T", #"3"], Nnrml), ([#"C"], Nnrml),
           ([#"T", #"C", #"1"], Nnrml), ([#"T", #"C", #"2"], Nnrml),
           ([#"v", #"1"], Nnrml), ([#"v", #"2"], Nnrml), ([#"w"], Nnrml),
           ([#"w", #"i", #"n", #"1"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"1"], Nnrml),
           ([#"w", #"i", #"n", #"2"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"2"], Nnrml),
           ([#"w", #"i", #"n", #"3"], Nnrml),
           ([#"w", #"o", #"u", #"t", #"3"], Nnrml), ([#"w", #"i", #"n"], Nnrml),
           ([#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"], Nnrml),
           ([#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
              #"2"],
             Nnrml),
           ([#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
              #"3"],
             Nnrml),
           ([#"C", #"_", #"v", #"1", #"_", #"v", #"2"], Nnrml),
           ([#"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i", #"n"],
             Nnrml),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
             Nprxy),
           ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"], Nprxy),
           ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
              #"_", #"w", #"i", #"n"],
             Nprxy),
           ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
              #"_", #"w", #"o", #"u", #"t"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
              #"r", #"_", #"v", #"1"],
             Nprxy),
           ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
              #"r", #"_", #"w", #"i", #"n"],
             Nprxy)],
          [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"], Elnk),
            ([#"E", #"C", #"D", #"_", #"V"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"], Elnk),
            ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"], Elnk),
            ([#"E", #"C", #"D", #"_", #"C"], Elnk),
            ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"], Elnk),
            ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"], Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
               #"1"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
               #"_", #"w", #"i", #"n", #"2"],
              Elnk),
            ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
               #"_", #"w", #"i", #"n", #"3"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1"], Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"i", #"n"], Elnk),
            ([#"E", #"_", #"V", #"_", #"v", #"2"], Elnk),
            ([#"E", #"_", #"V", #"_", #"w"], Elnk),
            ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
              Elnk),
            ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
               #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
               #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
               #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
               #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
               #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
               #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
               #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
               #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
               #"i", #"n", #"_", #"s", #"r", #"c"],
              Elnk),
            ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
               #"i", #"n", #"_", #"t", #"g", #"t"],
              Elnk),
            ([#"E", #"T", #"C", #"1", #"_", #"V"], Elnk),
            ([#"E", #"T", #"C", #"1", #"_", #"W", #"T", #"1"], Elnk),
            ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"2"], Elnk),
            ([#"E", #"T", #"C", #"2", #"_", #"W", #"T", #"3"], Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"1"],
              Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"T", #"C", #"2"],
              Elnk),
            ([#"E", #"W", #"T", #"S", #"y", #"s", #"_", #"C"], Elnk),
            ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"], Elnk),
            ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
              Elnk),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"], Eref),
            ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"1"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
               #"n", #"t", #"r", #"o", #"l", #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
               #"l", #"e", #"r"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
               #"2"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k", #"_", #"w", #"i", #"n"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
               #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
               #"l", #"e", #"r", #"_", #"v", #"1"],
              Eref),
            ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
               #"l", #"e", #"r", #"_", #"w", #"i", #"n"],
              Eref)],
          [], [], ()));

val f_CD_3WTs_loop : unit fr_ls_ext =
  Fr_ls_ext
    (sG_CD_3WTs_loop,
      [([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k"],
         [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"V", #"a", #"l", #"v", #"e"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"1"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o",
            #"l", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"V", #"a", #"l", #"v", #"e", #"_", #"w"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"i", #"n"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w",
            #"o", #"u", #"t"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"v", #"1"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"w", #"i", #"n"],
          [#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_",
            #"w", #"i", #"n"])],
      ());

val mdl_3WTs_loop : unit mdl_ls_ext =
  Mdl_ls_ext
    (gFG_3WTs_loop,
      [([#"F", #"_", #"A", #"S", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
          #"o", #"o", #"p"],
         f_ASD_3WTs_loop),
        ([#"F", #"_", #"C", #"D", #"_", #"3", #"W", #"T", #"s", #"_", #"l",
           #"o", #"o", #"p"],
          f_CD_3WTs_loop)],
      ());

val t_F_ASD_3WTs_loop : unit morphL_ext =
  MorphL_ext
    ([([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A", #"S",
         #"D"],
        [#"A", #"S", #"D"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"S", #"y",
          #"s"],
         [#"S", #"y", #"s", #"t", #"e", #"m"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"1"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"2"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s", #"3"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
          #"1"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
          #"2"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v", #"e"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e", #"r", #"T",
          #"a", #"n", #"k"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n",
          #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e", #"r", #"T",
          #"a", #"n", #"k"],
         [#"C", #"o", #"m", #"p", #"o", #"s", #"i", #"t", #"i", #"o", #"n"]),
       ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r"],
         [#"E", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e"],
         [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
         [#"P", #"O", #"C", #"o", #"m", #"p", #"o", #"n", #"e", #"n", #"t"]),
       ([#"F", #"l", #"o", #"w", #"R", #"a", #"t", #"e"],
         [#"D", #"T", #"y", #"p", #"e"]),
       ([#"A", #"r", #"e", #"a"], [#"D", #"T", #"y", #"p", #"e"]),
       ([#"H", #"e", #"i", #"g", #"h", #"t"], [#"D", #"T", #"y", #"p", #"e"]),
       ([#"O", #"p", #"e", #"n", #"C", #"l", #"o", #"s", #"e", #"d"],
         [#"E", #"n", #"u", #"m", #"e", #"r", #"a", #"t", #"i", #"o", #"n"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"i",
          #"n"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_", #"w", #"o",
          #"u", #"t"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"V", #"a", #"l", #"v", #"e", #"_", #"w"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"v",
          #"1"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"]),
       ([#"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r", #"_", #"w",
          #"i", #"n"],
         [#"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t"])],
      [([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s", #"A",
          #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n",
          #"k", #"s", #"S", #"y", #"s"],
         [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"V", #"a", #"l", #"v", #"e"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"E", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"F", #"l", #"o", #"w", #"R", #"a", #"t",
           #"e"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"A", #"r", #"e", #"a"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"H", #"e", #"i", #"g", #"h", #"t"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"s",
           #"A", #"S", #"D", #"_", #"O", #"p", #"e", #"n", #"C", #"l", #"o",
           #"s", #"e", #"d"],
          [#"E", #"t", #"y", #"p", #"e", #"s"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"s", #"r",
           #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"1", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"2", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"W", #"a", #"t", #"e", #"r", #"T",
           #"a", #"n", #"k", #"s", #"S", #"y", #"s", #"3", #"_", #"t", #"g",
           #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"s", #"r", #"c"],
          [#"E", #"s", #"r", #"c"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"V", #"a", #"l", #"v",
           #"e", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"1", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"C", #"o", #"m", #"p", #"T", #"a", #"n", #"k", #"s", #"C",
           #"o", #"n", #"t", #"r", #"o", #"l", #"2", #"W", #"a", #"t", #"e",
           #"r", #"T", #"a", #"n", #"k", #"_", #"t", #"g", #"t"],
          [#"E", #"t", #"g", #"t"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"w", #"i", #"n"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k",
           #"_", #"o", #"u", #"t"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"v", #"1"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
           #"r", #"_", #"w", #"i", #"n"],
          [#"E", #"B", #"l", #"o", #"c", #"k", #"P", #"r", #"o", #"p", #"s"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"_", #"v", #"2"],
          [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
            #"p", #"e", #"n", #"d", #"s"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"w", #"o", #"u", #"t", #"_",
           #"w", #"i", #"n"],
          [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
            #"p", #"e", #"n", #"d", #"s"]),
        ([#"E", #"_", #"D", #"e", #"p", #"_", #"v", #"1", #"_", #"w", #"i",
           #"n"],
          [#"E", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"D", #"e",
            #"p", #"e", #"n", #"d", #"s"])],
      ());

val t_F_CD_3WTs_loop : unit morphL_ext =
  MorphL_ext
    ([([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k"],
        [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
          #"o", #"l", #"1"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o", #"n", #"t", #"r",
          #"o", #"l", #"2"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e",
          #"r"],
         [#"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
       ([#"C", #"D", #"_", #"3", #"W", #"T", #"s"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"i", #"o", #"n", #"s",
           #"D", #"i", #"a", #"g", #"r", #"a", #"m"]),
       ([#"W", #"T", #"S", #"y", #"s"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"V"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"1"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"2"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"W", #"T", #"3"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"C"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"T", #"C", #"1"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"T", #"C", #"2"],
         [#"B", #"l", #"o", #"c", #"k", #"I", #"n", #"s", #"t", #"a", #"n",
           #"c", #"e"]),
       ([#"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w", #"i", #"n",
          #"2"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w", #"i", #"n",
          #"3"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"v", #"1", #"_", #"v", #"2"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w", #"i", #"n"],
         [#"C", #"o", #"n", #"n", #"e", #"c", #"t", #"o", #"r"]),
       ([#"v", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n"], [#"P", #"o", #"r", #"t"]),
       ([#"v", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"1"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"2"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"i", #"n", #"3"], [#"P", #"o", #"r", #"t"]),
       ([#"w", #"o", #"u", #"t", #"3"], [#"P", #"o", #"r", #"t"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v", #"2"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"i", #"n"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a", #"n", #"k", #"_",
          #"w", #"o", #"u", #"t"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"v", #"1"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"]),
       ([#"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l", #"l", #"e", #"r",
          #"_", #"w", #"i", #"n"],
         [#"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r", #"t", #"2"])],
      [([#"E", #"C", #"D", #"_", #"W", #"T", #"S", #"y", #"s"],
         [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"V"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"1"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"2"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"W", #"T", #"3"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"1"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"T", #"C", #"2"],
          [#"E", #"C", #"D", #"b", #"l", #"o", #"c", #"k", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n",
           #"1"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1",
           #"_", #"w", #"i", #"n", #"2"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"C", #"D", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2",
           #"_", #"w", #"i", #"n", #"3"],
          [#"E", #"C", #"D", #"c", #"o", #"n", #"n", #"e", #"c", #"t", #"o",
            #"r", #"s"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"s",
           #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1", #"_", #"v", #"2", #"_", #"t",
           #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"_", #"w", #"i", #"n", #"1", #"_",
           #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"w",
           #"i", #"n", #"2", #"_", #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"w",
           #"i", #"n", #"3", #"_", #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"s", #"r", #"c"],
          [#"E", #"C", #"_", #"s", #"r", #"c"]),
        ([#"E", #"_", #"C", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"w",
           #"i", #"n", #"_", #"t", #"g", #"t"],
          [#"E", #"C", #"_", #"t", #"g", #"t"]),
        ([#"E", #"_", #"C", #"_", #"v", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"C", #"_", #"w", #"i", #"n"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"V", #"_", #"v", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"V", #"_", #"w"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"i", #"n", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"1", #"_", #"w", #"o", #"u", #"t", #"1"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"i", #"n", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"2", #"_", #"w", #"o", #"u", #"t", #"2"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"i", #"n", #"3"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"W", #"T", #"3", #"_", #"w", #"o", #"u", #"t", #"3"],
          [#"E", #"B", #"I", #"p", #"o", #"r", #"t", #"s"]),
        ([#"E", #"_", #"v", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"v", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"1", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"2", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"i", #"n", #"3", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"_", #"w", #"o", #"u", #"t", #"3", #"_", #"t", #"y"],
          [#"E", #"P", #"o", #"r", #"t", #"T", #"y", #"p", #"e"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"1"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"T", #"a", #"n", #"k", #"s", #"C", #"o",
           #"n", #"t", #"r", #"o", #"l", #"2"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r"],
          [#"E", #"R", #"P", #"r", #"B", #"l", #"o", #"c", #"k", #"3"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"v",
           #"2"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"V", #"a", #"l", #"v", #"e", #"_", #"w"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"i", #"n"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"W", #"a", #"t", #"e", #"r", #"T", #"a",
           #"n", #"k", #"_", #"w", #"o", #"u", #"t"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"v", #"1"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"]),
        ([#"E", #"R", #"P", #"r", #"C", #"o", #"n", #"t", #"r", #"o", #"l",
           #"l", #"e", #"r", #"_", #"w", #"i", #"n"],
          [#"E", #"R", #"P", #"r", #"F", #"l", #"o", #"w", #"P", #"o", #"r",
            #"t", #"2"])],
      ());

val mdlTy_3WTs_loop : unit mdlTy_ls_ext =
  MdlTy_ls_ext
    (iNTO_SysML_MM_T, mdl_3WTs_loop, consUGM t_F_ASD_3WTs_loop t_F_CD_3WTs_loop,
      ());

val cSP_output_dir : char list =
  [#"/", #"U", #"s", #"e", #"r", #"s", #"/", #"w", #"v", #"8", #"5", #"9", #"9",
    #"/", #"W", #"o", #"r", #"k", #"/", #"F", #"r", #"a", #"g", #"m", #"e",
    #"n", #"t", #"a", #"/", #"I", #"s", #"a", #"b", #"e", #"l", #"l", #"e",
    #"/", #"I", #"N", #"T", #"O", #"-", #"C", #"P", #"S", #"/", #"C", #"S",
    #"P", #"/"];

val alloy_output_dir : char list =
  [#"/", #"U", #"s", #"e", #"r", #"s", #"/", #"w", #"v", #"8", #"5", #"9", #"9",
    #"/", #"W", #"o", #"r", #"k", #"/", #"F", #"r", #"a", #"g", #"m", #"e",
    #"n", #"t", #"a", #"/", #"I", #"s", #"a", #"b", #"e", #"l", #"l", #"e",
    #"/", #"I", #"N", #"T", #"O", #"-", #"C", #"P", #"S", #"/", #"A", #"l",
    #"l", #"o", #"y", #"/"];

end; (*struct CSP_Alloy*)
