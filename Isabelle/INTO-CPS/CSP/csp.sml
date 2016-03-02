structure CSP : sig
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
  datatype cSPSpec = Csp of decl list
  type 'a gr_ls_ext
  val str_int : int -> char list
  val g1 : unit gr_ls_ext
  val g2 : unit gr_ls_ext
  val g3 : unit gr_ls_ext
  val toCSP : unit gr_ls_ext -> cSPSpec
  val g3b : unit gr_ls_ext
  val g4a : unit gr_ls_ext
  val g4b : unit gr_ls_ext
  val output_dir : char list
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

datatype cSPSpec = Csp of decl list;

datatype 'a gr_ext =
  Gr_ext of
    (char list) set * (char list) set * (char list -> (char list) option) *
      (char list -> (char list) option) * 'a;

datatype 'a gr_ls_ext =
  Gr_ls_ext of
    (char list) list * (char list) list * (char list * char list) list *
      (char list * char list) list * 'a;

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

fun null [] = true
  | null (x :: xs) = false;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

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

fun size_list x = gen_length Zero_nat x;

fun enum xs = zip xs (upt Zero_nat (size_list xs));

val g1 : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"a"], [#"b", #"1"], [#"b", #"3"], [#"b", #"2"], [#"b", #"4"],
       [#"c", #"1"], [#"c", #"3"], [#"c", #"2"], [#"d", #"1"], [#"d", #"2"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"],
        [#"e", #"6"], [#"e", #"7"], [#"e", #"8"], [#"e", #"9"]],
      [([#"e", #"1"], [#"a"]), ([#"e", #"2"], [#"b", #"1"]),
        ([#"e", #"3"], [#"b", #"3"]), ([#"e", #"4"], [#"b", #"2"]),
        ([#"e", #"5"], [#"b", #"4"]), ([#"e", #"6"], [#"c", #"3"]),
        ([#"e", #"7"], [#"c", #"2"]), ([#"e", #"8"], [#"d", #"1"]),
        ([#"e", #"9"], [#"d", #"2"])],
      [([#"e", #"1"], [#"b", #"1"]), ([#"e", #"2"], [#"b", #"4"]),
        ([#"e", #"3"], [#"b", #"2"]), ([#"e", #"4"], [#"c", #"1"]),
        ([#"e", #"5"], [#"c", #"3"]), ([#"e", #"6"], [#"c", #"2"]),
        ([#"e", #"7"], [#"d", #"1"]), ([#"e", #"8"], [#"d", #"2"]),
        ([#"e", #"9"], [#"b", #"3"])],
      ());

val g2 : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"a"], [#"b", #"1"], [#"b", #"3"], [#"b", #"2"], [#"b", #"4"],
       [#"c", #"1"], [#"c", #"3"], [#"c", #"2"], [#"d", #"1"], [#"d", #"2"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"],
        [#"e", #"6"], [#"e", #"7"], [#"e", #"8"], [#"e", #"9"],
        [#"e", #"1", #"0"]],
      [([#"e", #"1"], [#"a"]), ([#"e", #"2"], [#"b", #"1"]),
        ([#"e", #"3"], [#"b", #"3"]), ([#"e", #"4"], [#"b", #"2"]),
        ([#"e", #"5"], [#"b", #"4"]), ([#"e", #"6"], [#"c", #"3"]),
        ([#"e", #"7"], [#"c", #"2"]), ([#"e", #"8"], [#"d", #"1"]),
        ([#"e", #"9"], [#"d", #"2"]), ([#"e", #"1", #"0"], [#"c", #"1"])],
      [([#"e", #"1"], [#"b", #"1"]), ([#"e", #"2"], [#"b", #"4"]),
        ([#"e", #"3"], [#"b", #"2"]), ([#"e", #"4"], [#"c", #"1"]),
        ([#"e", #"5"], [#"c", #"3"]), ([#"e", #"6"], [#"c", #"2"]),
        ([#"e", #"7"], [#"d", #"1"]), ([#"e", #"8"], [#"d", #"2"]),
        ([#"e", #"9"], [#"b", #"3"]), ([#"e", #"1", #"0"], [#"c", #"2"])],
      ());

val g3 : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"y", #"1"], [#"y", #"2"], [#"x"], [#"y"], [#"s"], [#"x", #"1"],
       [#"x", #"2"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"],
        [#"e", #"6"]],
      [([#"e", #"1"], [#"y", #"1"]), ([#"e", #"2"], [#"y", #"2"]),
        ([#"e", #"3"], [#"y", #"2"]), ([#"e", #"4"], [#"s"]),
        ([#"e", #"5"], [#"y"]), ([#"e", #"6"], [#"x"])],
      [([#"e", #"1"], [#"x"]), ([#"e", #"2"], [#"s"]),
        ([#"e", #"3"], [#"x", #"2"]), ([#"e", #"4"], [#"y"]),
        ([#"e", #"5"], [#"x", #"1"]), ([#"e", #"6"], [#"y"])],
      ());

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

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun src (Gr_ext (ns, es, src, tgt, more)) = src;

fun incidentEsSrc_ls_0 [] gl v = []
  | incidentEsSrc_ls_0 (e :: el) gl v =
    let
      val el2 = incidentEsSrc_ls_0 el gl v;
    in
      (if equal_option (equal_list equal_char) (src gl e) (SOME v) then e :: el2
        else el2)
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

val g3b : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"y", #"1"], [#"y", #"2"], [#"x"], [#"y"], [#"s"], [#"x", #"1"],
       [#"x", #"2"], [#"y", #"3"], [#"x", #"0"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"],
        [#"e", #"6"], [#"e", #"7"], [#"e", #"8"], [#"e", #"9"]],
      [([#"e", #"1"], [#"y", #"1"]), ([#"e", #"2"], [#"y", #"2"]),
        ([#"e", #"3"], [#"y", #"2"]), ([#"e", #"4"], [#"s"]),
        ([#"e", #"5"], [#"y"]), ([#"e", #"6"], [#"x"]),
        ([#"e", #"7"], [#"x", #"1"]), ([#"e", #"8"], [#"y", #"3"]),
        ([#"e", #"9"], [#"x", #"0"])],
      [([#"e", #"1"], [#"x"]), ([#"e", #"2"], [#"s"]),
        ([#"e", #"3"], [#"x", #"2"]), ([#"e", #"4"], [#"y"]),
        ([#"e", #"5"], [#"x", #"1"]), ([#"e", #"6"], [#"y"]),
        ([#"e", #"7"], [#"y", #"3"]), ([#"e", #"8"], [#"x", #"0"]),
        ([#"e", #"9"], [#"y", #"1"])],
      ());

val g4a : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"u"], [#"y", #"1"], [#"y", #"2"], [#"x"], [#"y"], [#"z"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"]],
      [([#"e", #"1"], [#"x"]), ([#"e", #"2"], [#"y"]), ([#"e", #"3"], [#"u"]),
        ([#"e", #"4"], [#"y", #"2"]), ([#"e", #"5"], [#"y", #"1"])],
      [([#"e", #"1"], [#"y"]), ([#"e", #"2"], [#"u"]),
        ([#"e", #"3"], [#"y", #"2"]), ([#"e", #"4"], [#"z"]),
        ([#"e", #"5"], [#"x"])],
      ());

val g4b : unit gr_ls_ext =
  Gr_ls_ext
    ([[#"u"], [#"y", #"1"], [#"y", #"2"], [#"x"], [#"y"], [#"z"]],
      [[#"e", #"1"], [#"e", #"2"], [#"e", #"3"], [#"e", #"4"], [#"e", #"5"]],
      [([#"e", #"1"], [#"x"]), ([#"e", #"2"], [#"y"]), ([#"e", #"3"], [#"u"]),
        ([#"e", #"4"], [#"y", #"2"]), ([#"e", #"5"], [#"y", #"1"])],
      [([#"e", #"1"], [#"y"]), ([#"e", #"2"], [#"u"]),
        ([#"e", #"3"], [#"y", #"2"]), ([#"e", #"4"], [#"x"]),
        ([#"e", #"5"], [#"z"])],
      ());

val output_dir : char list =
  [#"/", #"U", #"s", #"e", #"r", #"s", #"/", #"w", #"v", #"8", #"5", #"9", #"9",
    #"/", #"W", #"o", #"r", #"k", #"/", #"F", #"r", #"a", #"g", #"m", #"e",
    #"n", #"t", #"a", #"/", #"I", #"s", #"a", #"b", #"e", #"l", #"l", #"e",
    #"/", #"I", #"N", #"T", #"O", #"-", #"C", #"P", #"S", #"/", #"C", #"S",
    #"P", #"/"];

end; (*struct CSP*)
