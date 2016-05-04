structure PDGs : sig
  type nibble
  type 'a gr_ls_ext
  val g1 : unit gr_ls_ext
  val g2 : unit gr_ls_ext
  val g3 : unit gr_ls_ext
  val g3b : unit gr_ls_ext
  val g4a : unit gr_ls_ext
  val g4b : unit gr_ls_ext
end = struct

datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;

datatype 'a gr_ls_ext =
  Gr_ls_ext of
    (char list) list * (char list) list * (char list * char list) list *
      (char list * char list) list * 'a;

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

end; (*struct PDGs*)
